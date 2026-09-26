package checker

import (
	"os"
	"slices"

	"github.com/microsoft/typescript-go/internal/ast"
	"github.com/microsoft/typescript-go/internal/collections"
	"github.com/microsoft/typescript-go/internal/core"
)

// Resolving the members of an instantiated class or interface reference
// instantiates every declared member and merges every inherited one, even when
// the caller only wants one property (`expect(x).toBe`, `schema.optional`,
// `arr.map`). In large programs most of those symbols are never used. For a
// by-name lookup we instantiate just the requested member; if the full table
// is built later it reuses the symbols handed out here, so identities match.

var lazyMembersEnabled = os.Getenv("TSGO_LAZY_MEMBERS") != "0"

type lazyMemberTable struct {
	mapper        *TypeMapper
	typeArguments []*Type
	declared      map[string]*ast.Symbol // instantiated declared members, by name
	found         map[string]*ast.Symbol // memoized lookups; nil means no such member
	inProgress    map[string]bool

	declaredIndexInfos         []*IndexInfo // instantiated declared index infos
	declaredIndexInfosComputed bool
	indexInfos                 []*IndexInfo // declared plus inherited, as full resolution merges them
	indexInfosComputed         bool
	indexInfosInProgress       bool
}

func (c *Checker) referenceMemberTypeArguments(t *Type, source *Type) (typeParameters []*Type, typeArguments []*Type) {
	typeParameters = source.AsInterfaceType().allTypeParameters
	typeArguments = c.getTypeArguments(t)
	if len(typeArguments) == len(typeParameters)-1 {
		typeArguments = core.Concatenate(typeArguments, []*Type{t})
	}
	return typeParameters, typeArguments
}

func (c *Checker) getLazyMemberTable(t *Type) *lazyMemberTable {
	if !lazyMembersEnabled {
		return nil
	}
	if t.objectFlags&(ObjectFlagsMembersResolved|ObjectFlagsReference) != ObjectFlagsReference {
		return nil
	}
	if lm := c.lazyMemberTables[t]; lm != nil {
		return lm
	}
	source := t.Target()
	if source == nil || source == t || source.objectFlags&ObjectFlagsClassOrInterface == 0 || source.objectFlags&ObjectFlagsTuple != 0 {
		return nil
	}
	if t.symbol != nil && t.symbol.Flags&ast.SymbolFlagsValueModule != 0 {
		return nil
	}
	typeParameters, typeArguments := c.referenceMemberTypeArguments(t, source)
	if slices.Equal(typeParameters, typeArguments) {
		return nil
	}
	lm := &lazyMemberTable{
		mapper:        newTypeMapper(typeParameters, typeArguments),
		typeArguments: typeArguments,
		declared:      map[string]*ast.Symbol{},
		found:         map[string]*ast.Symbol{},
		inProgress:    map[string]bool{},
	}
	if c.lazyMemberTables == nil {
		c.lazyMemberTables = map[*Type]*lazyMemberTable{}
	}
	c.lazyMemberTables[t] = lm
	return lm
}

// lookupMemberLazily returns what resolveStructuredTypeMembers(t).members[name]
// would hold, without building t's member table. ok is false when the lazy
// path can't answer and the caller must resolve members normally.
func (c *Checker) lookupMemberLazily(t *Type, name string) (symbol *ast.Symbol, ok bool) {
	if isReservedMemberName(name) {
		return nil, false
	}
	lm := c.getLazyMemberTable(t)
	if lm == nil {
		return nil, false
	}
	if symbol, ok := lm.found[name]; ok {
		return symbol, true
	}
	if lm.inProgress[name] {
		return nil, false
	}
	lm.inProgress[name] = true
	defer delete(lm.inProgress, name)
	source := t.Target()
	// Mirrors resolveObjectTypeMembers: declared named members first, then
	// inherited properties, where a base may only fill a missing or non-value
	// entry (addInheritedMembers).
	var result *ast.Symbol
	if decl := c.resolveDeclaredMembers(source).declaredMembers[name]; decl != nil && c.isNamedMember(decl, name) {
		result = lm.declared[name]
		if result == nil {
			result = c.instantiateSymbol(decl, lm.mapper)
			lm.declared[name] = result
		}
	}
	thisArgument := core.LastOrNil(lm.typeArguments)
	for _, baseType := range c.getBaseTypes(source) {
		if result != nil && result.Flags&ast.SymbolFlagsValue != 0 {
			break
		}
		instantiatedBaseType := baseType
		if thisArgument != nil {
			instantiatedBaseType = c.getTypeWithThisArgument(c.instantiateType(baseType, lm.mapper), thisArgument, false /*needsApparentType*/)
		}
		if prop := c.getNamedPropertyOfType(instantiatedBaseType, name); prop != nil && !isStaticPrivateIdentifierProperty(prop) {
			result = prop
		}
	}
	// A lookup above may have fully resolved t; its table is then authoritative.
	if t.objectFlags&ObjectFlagsMembersResolved != 0 && t.objectFlags&ObjectFlagsUnresolvedMembers == 0 {
		return t.AsStructuredType().members[name], true
	}
	lm.found[name] = result
	return result, true
}

// getNamedPropertyOfType finds name among getPropertiesOfType(t).
func (c *Checker) getNamedPropertyOfType(t *Type, name string) *ast.Symbol {
	reduced := c.getReducedApparentType(t)
	if reduced.flags&TypeFlagsObject != 0 {
		if symbol, ok := c.lookupMemberLazily(reduced, name); ok {
			return symbol
		}
		if symbol := c.resolveStructuredTypeMembers(reduced).members[name]; symbol != nil && c.isNamedMember(symbol, name) {
			return symbol
		}
		return nil
	}
	for _, prop := range c.getPropertiesOfType(t) {
		if prop.Name == name {
			return prop
		}
	}
	return nil
}

// takeLazyMemberTable hands the members created lazily for t to full member
// resolution, which must reuse them.
func (c *Checker) takeLazyMemberTable(t *Type) *lazyMemberTable {
	lm := c.lazyMemberTables[t]
	if lm != nil {
		delete(c.lazyMemberTables, t)
	}
	return lm
}

// getDeclaredShape returns the resolved generic declaration behind an
// instantiated class or interface reference whose own members aren't resolved
// yet. Instantiation maps members, signatures and index infos one to one, so
// the declaration answers shape questions (how many properties, signatures and
// index infos; which properties are optional) without resolving t.
func (c *Checker) getDeclaredShape(t *Type) *StructuredType {
	if !lazyMembersEnabled || t.flags&TypeFlagsObject == 0 || t.objectFlags&(ObjectFlagsMembersResolved|ObjectFlagsReference) != ObjectFlagsReference {
		return nil
	}
	source := t.Target()
	if source == nil || source == t || source.objectFlags&ObjectFlagsClassOrInterface == 0 || source.objectFlags&ObjectFlagsTuple != 0 {
		return nil
	}
	if t.symbol != nil && t.symbol.Flags&ast.SymbolFlagsValueModule != 0 {
		return nil
	}
	// Full resolution always resolves type arguments first, which is where
	// circular references (TS4109) are reported; keep that ordering.
	c.getTypeArguments(t)
	if t.objectFlags&ObjectFlagsMembersResolved != 0 {
		return nil
	}
	shape := c.resolveStructuredTypeMembers(source)
	if source.objectFlags&ObjectFlagsUnresolvedMembers != 0 {
		// Still merging inherited members; the declaration's shape is partial.
		return nil
	}
	return shape
}

// getIndexInfosLazily computes resolveStructuredTypeMembers(t).indexInfos
// without instantiating t's members (e.g. `arr[i]` on an Array<T>).
func (c *Checker) getIndexInfosLazily(t *Type) ([]*IndexInfo, bool) {
	lm := c.getLazyMemberTable(t)
	if lm == nil || lm.indexInfosInProgress {
		return nil, false
	}
	if lm.indexInfosComputed {
		return lm.indexInfos, true
	}
	lm.indexInfosInProgress = true
	defer func() { lm.indexInfosInProgress = false }()
	source := t.Target()
	indexInfos := c.getLazyDeclaredIndexInfos(lm, source)
	if baseTypes := c.getBaseTypes(source); len(baseTypes) != 0 {
		thisArgument := core.LastOrNil(lm.typeArguments)
		for _, baseType := range baseTypes {
			instantiatedBaseType := baseType
			if thisArgument != nil {
				instantiatedBaseType = c.getTypeWithThisArgument(c.instantiateType(baseType, lm.mapper), thisArgument, false /*needsApparentType*/)
			}
			var inheritedIndexInfos []*IndexInfo
			if instantiatedBaseType != c.anyType {
				inheritedIndexInfos = c.getIndexInfosOfType(instantiatedBaseType)
			} else {
				inheritedIndexInfos = []*IndexInfo{c.anyBaseTypeIndexInfo}
			}
			indexInfos = core.Concatenate(indexInfos, core.Filter(inheritedIndexInfos, func(info *IndexInfo) bool {
				return findIndexInfo(indexInfos, info.keyType) == nil
			}))
		}
	}
	if t.objectFlags&ObjectFlagsMembersResolved != 0 && t.objectFlags&ObjectFlagsUnresolvedMembers == 0 {
		return t.AsStructuredType().indexInfos, true
	}
	lm.indexInfos = indexInfos
	lm.indexInfosComputed = true
	return indexInfos, true
}

func (c *Checker) getLazyDeclaredIndexInfos(lm *lazyMemberTable, source *Type) []*IndexInfo {
	if !lm.declaredIndexInfosComputed {
		lm.declaredIndexInfos = c.instantiateIndexInfos(c.resolveDeclaredMembers(source).declaredIndexInfos, lm.mapper)
		lm.declaredIndexInfosComputed = true
	}
	return lm.declaredIndexInfos
}

var lazyReduceEnabled = os.Getenv("TSGO_LAZY_REDUCE") != "0"

// isNeverReducedIntersection answers
// core.Some(getPropertiesOfUnionOrIntersectionType(t), isNeverReducedProperty)
// without building a synthetic property for every name. Only a name shared by
// several constituents where one has a literal type (a discriminant) or a
// private declaration can reduce the intersection to never, so other names
// are skipped; candidates go through the exact check.
func (c *Checker) isNeverReducedIntersection(t *Type) bool {
	var checked collections.Set[string]
	for _, current := range t.Types() {
		for _, prop := range c.getPropertiesOfType(current) {
			if checked.Has(prop.Name) {
				continue
			}
			checked.Add(prop.Name)
			if !c.mayBeNeverReducedIntersectionProperty(t, prop.Name) {
				continue
			}
			if combined := c.getPropertyOfUnionOrIntersectionType(t, prop.Name, true /*skipObjectFunctionPropertyAugment*/); combined != nil && c.isNeverReducedProperty(combined) {
				return true
			}
		}
	}
	return false
}

func (c *Checker) mayBeNeverReducedIntersectionProperty(t *Type, name string) bool {
	// Mirrors how createUnionOrIntersectionProperty collects constituent properties.
	var props []*ast.Symbol
	for _, current := range t.Types() {
		apparent := c.getApparentType(current)
		if c.isErrorType(apparent) || apparent.flags&TypeFlagsNever != 0 {
			continue
		}
		if prop := c.getPropertyOfTypeEx(apparent, name, true /*skipObjectFunctionPropertyAugment*/, false); prop != nil {
			if prop.CheckFlags&(ast.CheckFlagsNonUniformAndLiteral|ast.CheckFlagsContainsPrivate) != 0 || getDeclarationModifierFlagsFromSymbol(prop)&ast.ModifierFlagsPrivate != 0 {
				return true
			}
			props = append(props, prop)
		}
	}
	if len(props) < 2 {
		return false
	}
	for _, prop := range props {
		if propType := c.getTypeOfSymbol(prop); isLiteralType(propType) || c.isPatternLiteralType(propType) {
			return true
		}
	}
	return false
}
