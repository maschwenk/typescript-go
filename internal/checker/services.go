package checker

import (
	"maps"
	"slices"

	"github.com/microsoft/typescript-go/internal/ast"
)

func (c *Checker) GetSymbolsInScope(location *ast.Node, meaning ast.SymbolFlags) []*ast.Symbol {
	return c.getSymbolsInScope(location, meaning)
}

func (c *Checker) getSymbolsInScope(location *ast.Node, meaning ast.SymbolFlags) []*ast.Symbol {
	if location.Flags&ast.NodeFlagsInWithStatement != 0 {
		// We cannot answer semantic questions within a with block, do not proceed any further
		return nil
	}

	symbols := createSymbolTable(nil)
	isStaticSymbol := false

	// Copy the given symbol into symbol tables if the symbol has the given meaning
	// and it doesn't already exists in the symbol table.
	copySymbol := func(symbol *ast.Symbol, meaning ast.SymbolFlags) {
		if getCombinedLocalAndExportSymbolFlags(symbol)&meaning != 0 {
			id := symbol.Name
			// We will copy all symbol regardless of its reserved name because
			// symbolsToArray will check whether the key is a reserved name and
			// it will not copy symbol with reserved name to the array
			if _, ok := symbols[id]; !ok {
				symbols[id] = symbol
			}
		}
	}

	copySymbols := func(source ast.SymbolTable, meaning ast.SymbolFlags) {
		if meaning != 0 {
			for _, symbol := range source {
				copySymbol(symbol, meaning)
			}
		}
	}

	copyLocallyVisibleExportSymbols := func(source ast.SymbolTable, meaning ast.SymbolFlags) {
		if meaning != 0 {
			for _, symbol := range source {
				// Similar condition as in `resolveNameHelper`
				if ast.GetDeclarationOfKind(symbol, ast.KindExportSpecifier) == nil &&
					ast.GetDeclarationOfKind(symbol, ast.KindNamespaceExport) == nil &&
					symbol.Name != ast.InternalSymbolNameDefault {
					copySymbol(symbol, meaning)
				}
			}
		}
	}

	populateSymbols := func() {
		for location != nil {
			if canHaveLocals(location) && location.Locals() != nil && !ast.IsGlobalSourceFile(location) {
				copySymbols(location.Locals(), meaning)
			}

			switch location.Kind {
			case ast.KindSourceFile:
				if !ast.IsExternalModule(location.AsSourceFile()) {
					break
				}
				fallthrough
			case ast.KindModuleDeclaration:
				copyLocallyVisibleExportSymbols(c.getSymbolOfDeclaration(location).Exports, meaning&ast.SymbolFlagsModuleMember)
			case ast.KindEnumDeclaration:
				copySymbols(c.getSymbolOfDeclaration(location).Exports, meaning&ast.SymbolFlagsEnumMember)
			case ast.KindClassExpression:
				className := location.AsClassExpression().Name()
				if className != nil {
					copySymbol(location.Symbol(), meaning)
				}
				// this fall-through is necessary because we would like to handle
				// type parameter inside class expression similar to how we handle it in classDeclaration and interface Declaration.
				fallthrough
			case ast.KindClassDeclaration, ast.KindInterfaceDeclaration:
				// If we didn't come from static member of class or interface,
				// add the type parameters into the symbol table
				// (type parameters of classDeclaration/classExpression and interface are in member property of the symbol.
				// Note: that the memberFlags come from previous iteration.
				if !isStaticSymbol {
					copySymbols(c.getMembersOfSymbol(c.getSymbolOfDeclaration(location)), meaning&ast.SymbolFlagsType)
				}
			case ast.KindFunctionExpression:
				funcName := location.Name()
				if funcName != nil {
					copySymbol(location.Symbol(), meaning)
				}
			}

			if introducesArgumentsExoticObject(location) {
				copySymbol(c.argumentsSymbol, meaning)
			}

			isStaticSymbol = ast.IsStatic(location)
			location = location.Parent
		}

		copySymbols(c.globals, meaning)
	}

	populateSymbols()

	delete(symbols, ast.InternalSymbolNameThis) // Not a symbol, a keyword
	return symbolsToArray(symbols)
}

func (c *Checker) GetAliasedSymbol(symbol *ast.Symbol) *ast.Symbol {
	return c.resolveAlias(symbol)
}

func (c *Checker) GetExportsOfModule(symbol *ast.Symbol) []*ast.Symbol {
	return symbolsToArray(c.getExportsOfModule(symbol))
}

func (c *Checker) IsValidPropertyAccess(node *ast.Node, propertyName string) bool {
	return c.isValidPropertyAccess(node, propertyName)
}

func (c *Checker) isValidPropertyAccess(node *ast.Node, propertyName string) bool {
	switch node.Kind {
	case ast.KindPropertyAccessExpression:
		return c.isValidPropertyAccessWithType(node, node.Expression().Kind == ast.KindSuperKeyword, propertyName, c.getWidenedType(c.checkExpression(node.Expression())))
	case ast.KindQualifiedName:
		return c.isValidPropertyAccessWithType(node, false /*isSuper*/, propertyName, c.getWidenedType(c.checkExpression(node.AsQualifiedName().Left)))
	case ast.KindImportType:
		return c.isValidPropertyAccessWithType(node, false /*isSuper*/, propertyName, c.getTypeFromTypeNode(node))
	}
	panic("Unexpected node kind in isValidPropertyAccess: " + node.Kind.String())
}

func (c *Checker) isValidPropertyAccessWithType(node *ast.Node, isSuper bool, propertyName string, t *Type) bool {
	// Short-circuiting for improved performance.
	if IsTypeAny(t) {
		return true
	}

	prop := c.getPropertyOfType(t, propertyName)
	return prop != nil && c.isPropertyAccessible(node, isSuper, false /*isWrite*/, t, prop)
}

// Checks if an existing property access is valid for completions purposes.
// node: a property access-like node where we want to check if we can access a property.
// This node does not need to be an access of the property we are checking.
// e.g. in completions, this node will often be an incomplete property access node, as in `foo.`.
// Besides providing a location (i.e. scope) used to check property accessibility, we use this node for
// computing whether this is a `super` property access.
// type: the type whose property we are checking.
// property: the accessed property's symbol.
func (c *Checker) IsValidPropertyAccessForCompletions(node *ast.Node, t *Type, property *ast.Symbol) bool {
	return c.isPropertyAccessible(
		node,
		node.Kind == ast.KindPropertyAccessExpression && node.Expression().Kind == ast.KindSuperKeyword,
		false, /*isWrite*/
		t,
		property,
	)
	// Previously we validated the 'this' type of methods but this adversely affected performance. See #31377 for more context.
}

func (c *Checker) GetAllPossiblePropertiesOfTypes(types []*Type) []*ast.Symbol {
	unionType := c.getUnionType(types)
	if unionType.flags&TypeFlagsUnion == 0 {
		return c.getAugmentedPropertiesOfType(unionType)
	}

	props := createSymbolTable(nil)
	for _, memberType := range types {
		augmentedProps := c.getAugmentedPropertiesOfType(memberType)
		for _, p := range augmentedProps {
			if _, ok := props[p.Name]; !ok {
				prop := c.createUnionOrIntersectionProperty(unionType, p.Name, false /*skipObjectFunctionPropertyAugment*/)
				// May be undefined if the property is private
				if prop != nil {
					props[p.Name] = prop
				}
			}
		}
	}
	return slices.Collect(maps.Values(props))
}

func (c *Checker) IsUnknownSymbol(symbol *ast.Symbol) bool {
	return symbol == c.unknownSymbol
}

// Originally from services.ts
func (c *Checker) GetNonOptionalType(t *Type) *Type {
	return c.removeOptionalTypeMarker(t)
}

func (c *Checker) GetStringIndexType(t *Type) *Type {
	return c.getIndexTypeOfType(t, c.stringType)
}

func (c *Checker) GetNumberIndexType(t *Type) *Type {
	return c.getIndexTypeOfType(t, c.numberType)
}

func (c *Checker) GetCallSignatures(t *Type) []*Signature {
	return c.getSignaturesOfType(t, SignatureKindCall)
}

func (c *Checker) GetConstructSignatures(t *Type) []*Signature {
	return c.getSignaturesOfType(t, SignatureKindConstruct)
}

func (c *Checker) GetApparentProperties(t *Type) []*ast.Symbol {
	return c.getAugmentedPropertiesOfType(t)
}

func (c *Checker) getAugmentedPropertiesOfType(t *Type) []*ast.Symbol {
	t = c.getApparentType(t)
	propsByName := createSymbolTable(c.getPropertiesOfType(t))
	var functionType *Type
	if len(c.getSignaturesOfType(t, SignatureKindCall)) > 0 {
		functionType = c.globalCallableFunctionType
	} else if len(c.getSignaturesOfType(t, SignatureKindConstruct)) > 0 {
		functionType = c.globalNewableFunctionType
	}

	if functionType != nil {
		for _, p := range c.getPropertiesOfType(functionType) {
			if _, ok := propsByName[p.Name]; !ok {
				propsByName[p.Name] = p
			}
		}
	}
	return c.getNamedMembers(propsByName)
}

func (c *Checker) IsUnion(t *Type) bool {
	return t.flags&TypeFlagsUnion != 0
}
