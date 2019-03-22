import macros, future, intsets
from sequtils import apply, map, zip, toSeq, applyIt, allIt, mapIt

## Classy
## ======
##
## Provides ability to define and instantiate haskell-like typeclasses in Nim.
##
## Overview
## --------
##
## This module consists of two macros. ``typeclass`` saves a parameterized AST to
## serve as a template (in an object of type ``Typeclass``). ``instance`` performs
## necessary substitutions in saved AST for provided arguments, and executes
## the resulting code.
##
## As an example, let's say we want to define a ``Functor`` typeclass:
##
## .. code-block:: nim
##   typeclass Functor, F[_]:
##     # proc fmap[A, B](fa: F[A], g: A -> B): F[B]
##     proc `$>`[A, B](fa: F[A], b: B): F[B]=
##       fmap(fa, (a: A) => b)
##
## This code does not declare any procs - only a compile-time variable ``Functor``.
## Notice that our code abstracts over type constructor - ``F`` is just a
## placeholder.
##
## Notice that ``fmap`` is not part of the typeclass. At the moment forward
## declarations don't work for generic procs in Nim. As we'll see, even if
## proc AST in our typeclass has no generic parameters, the generated proc
## can have some. So it is recommended to not define unimplemented procs
## inside typeclasses. This will probably change after this issue is closed:
## https://github.com/nim-lang/Nim/issues/4104.
##
## Now let's instantiate our typeclass. For example, let's define a ``Functor``
## instance for all tuples of two elements, where the left value is ``SomeInteger``:
##
## .. code-block:: nim
##
##   instance Functor, (C: SomeInteger) => (C, _)
##
## This generates the following proc definition:
##
## .. code-block:: nim
##
##   proc `$>`[A, B, C: SomeInteger](fa: (C, A), b: B): (C, B)=
##       fmap(fa, (a: A) => b)
##
## Here are the few things to notice:
##
## 1. All ocurrences of form ``F[X]`` were replaced with ``(C, X)``
## 2. ``C``, the parameter of our instance, became the parameter of the generated
##    definition, with its constraint preserved.
## 3. We're referring to a proc ``fmap``. So any procs, that are assumed to be
##    present in typeclass body, should be defined with corresponding types
##    before the typeclass is instantiated

type
  Unit = tuple[]

  AbstractPattern = object
    ## Type/pattern placeholder for typeclass declaration.
    ##
    ## Has either form ``A`` (placeholder for a concrete type) or ``A[_,...]`` (for
    ## a type constructor).
    ## Doesn't have to evaluate to concrete type after parameter substitution -
    ## must be eliminated after typeclass instantiation.
    ident: NimIdent
    arity: Natural
      ## types with arity of zero are considered concrete, with corresponding
      ## matching rules

  ConcretePattern = object
    ## A tree with zero or more wildcards (_).
    ##
    ## Should evaluate to concrete type once all the wildcards are replaced with
    ## types.
    tree: NimNode
    arity: Natural

  Typeclass* = object
    # Only here for better error messaging.
    # Do not use for membership checks and such!
    name: string
    patterns: seq[AbstractPattern]
    body: NimNode

  TypeclassMember = object
    patterns: seq[ConcretePattern]
    params: seq[NimNode]

  ExportOptionsKind = enum eoNone, eoSome, eoAll
  ExportOptions = object
    case kind: ExportOptionsKind
    of {eoNone, eoAll}: discard
    of eoSome:
      patterns: seq[NimNode]

  MemberOptions = object
    # Idents of the top-level procs to be skipped
    skipping: seq[NimNode]
    exporting: ExportOptions

  TypeclassOptions = object
    exported: bool

  # https://github.com/nim-lang/Nim/issues/4952
  GenTransformTuple[S] = object
    newNode: NimNode
    recurse: bool
    state: S

  TransformTuple = GenTransformTuple[Unit]

const unit: Unit = ()

proc mkGenTransformTuple[S](newNode: NimNode, recurse: bool, state: S): auto =
  GenTransformTuple[S](newNode: newNode, recurse: recurse, state: state)

proc mkTransformTuple(newNode: NimNode, recurse: bool): TransformTuple =
  mkGenTransformTuple(newNode, recurse, unit)

template fail(msg: string, n: NimNode = nil) =
  let errMsg = if n != nil: msg & ": " & $toStrLit(n) else: msg
  when compiles(error("", nil.NimNode)):
    error(errMsg, n)
  else:
    # Nim 0.15.2 and older
    error(errMsg)

proc arity(x: Typeclass): Natural {.compileTime.} =
  x.patterns.len

proc arity(x: TypeclassMember): Natural {.compileTime.} =
  x.patterns.len

proc replaceInBody(
  tree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)],
  substIndices: IntSet
): tuple[tree: NimNode, substIndices: IntSet]

proc transformDown[S](
  tree: NimNode,
  f: (n: NimNode, s: S) -> GenTransformTuple[S],
  s: S
): (NimNode, S) {.compileTime.} =
  let tup = f(tree.copyNimTree, s)
  var resNode = tup.newNode
  var resState = tup.state
  if tup.recurse:
    for i in 0..<resNode.len:
      var resSub: NimNode
      (resSub, resState) = transformDown(resNode[i], f, resState)
      resNode[i] = resSub

  (resNode, resState)

proc transformDown(
  tree: NimNode,
  f: (n: NimNode) -> TransformTuple
): NimNode {.compileTime.} =
  proc fs(n: NimNode, s: Unit): GenTransformTuple[Unit] {.closure.} =
    f(n)
  transformDown[tuple[]](
    tree = tree,
    f = fs,
    s = unit
  )[0]

proc asTree(p: AbstractPattern): NimNode {.compileTime.} =
  ## Restore `p`'s tree form
  ##
  ## Only useful for error messages - use fields for matching.
  if p.arity == 0:
    result = newIdentNode(p.ident)
  else:
    result = newTree(
      nnkBracketExpr,
      newIdentNode(p.ident)
    )
    for i in 1..p.arity:
      result.add(newIdentNode("_"))

proc getArity(tree: NimNode): int {.compileTime.} =
  ## Counts all underscore idents in ``tree``
  if tree.eqIdent("_"):
    result = 1
  else:
    result = 0
    for child in tree:
      result.inc(getArity(child))

proc matchesPattern(
  tree: NimNode, pattern: AbstractPattern
): bool {.compileTime.} =
  ## Checks whether ``tree`` is an occurence of ``pattern``
  ##
  ## Returns ``true`` if the patern matches, ``false`` otherwise.
  ## Raises if the arity does not match!
  if tree.eqIdent($pattern.ident):

    # TODO: This should happen at instantiation!
    # We should not allow invalid class body.
    if pattern.arity > 0:
      fail("Constructor pattern cannot be used without arguments", tree)

    # Concrete type - does not require brackets
    true

  elif tree.kind == nnkBracketExpr and
    tree.len > 0 and
    tree[0].eqIdent($pattern.ident):
    # Constructor - check arity
    let arity = tree.len - 1
    if arity != pattern.arity:
      let msg = "Wrong number of type arguments in expression " &
        "(expected " & $pattern.arity & ")"
      fail(msg, tree)

    true
  else:
    false

proc instantiateConstructor(
  concrete: ConcretePattern, abstract: AbstractPattern, tree: NimNode,
  processParam: NimNode -> NimNode
): NimNode {.compileTime.} =

  proc replaceUnderscores(
    tree: NimNode, args: seq[NimNode]
  ): (NimNode, seq[NimNode]) =
    var argsNew = args
    # Traverse ``tree`` and replace all underscore identifiers
    # with nodes from ``args`` in order.
    let treeNew = transformDown(tree) do (sub: NimNode) -> auto:
      if sub.eqIdent("_"):
        let res = argsNew[0].copyNimTree
        argsNew.delete(0)
        mkTransformTuple(res, false)
      else:
        mkTransformTuple(sub, true)

    (treeNew, argsNew)

  tree.expectKind(nnkBracketExpr)
  # First one is the constructor itself
  var args = toSeq(tree.children)
  args.delete(0)

  # we can have recursion in type arguments!
  args.apply(processParam)

  (result, args) = replaceUnderscores(concrete.tree, args)
  doAssert: args.len == 0

proc instantiate(
  concrete: ConcretePattern, abstract: AbstractPattern, tree: NimNode,
  processParam: NimNode -> NimNode
): NimNode {.compileTime.} =
  if abstract.arity > 0:
    concrete.instantiateConstructor(abstract, tree, processParam)
  else:
    # Members without parameters do not have brackets
    concrete.tree.copyNimTree

proc parseMemberParams(
  tree: NimNode
): seq[NimNode] =
  ## parse instance parameters in following forms:
  ## ``A``, ``(A, B)``, ``(A: T1, B)`` etc.

  if tree.kind == nnkPar:
    result = toSeq(tree.children)
  else:
    result = @[tree]

  for i in 0..<len(result):
    let n = result[i]
    if n.kind == nnkExprColonExpr:
      result[i] = newIdentDefs(n[0], n[1])
    else:
      result[i] = newIdentDefs(n, newEmptyNode())

proc parseAbstractPattern(
  tree: NimNode
): AbstractPattern {.compileTime.}  =
  ## Parses abstract pattern in forms ``A`` and ``A[_,...]``
  let wildcard = newIdentNode("_")
  let isValid = tree.kind == nnkIdent or (
    tree.kind == nnkBracketExpr and
    tree.len > 1 and
    tree[0].kind == nnkIdent and
    (toSeq(tree.children))[1..tree.len-1].allIt(it == wildcard)
  )

  if not isValid:
    fail("Illegal typeclass parameter expression", tree)

  if tree.kind == nnkBracketExpr:
    AbstractPattern(
      ident: tree[0].ident,
      arity: tree.len - 1
    )
  else:
    AbstractPattern(ident: tree.ident, arity: 0)

proc parseAbstractPatterns(
  tree: NimNode
): seq[AbstractPattern] {.compileTime.} =
  let patternNodes = (block:
    if tree.kind == nnkBracket:
      toSeq(tree.children)
    else:
      @[tree]
  )
  patternNodes.map(parseAbstractPattern)

proc replace(n: NimNode, subst: seq[(NimNode, NimNode)]): NimNode {.compileTime.} =
  transformDown(n) do (sub: NimNode) -> auto:
    for pair in subst:
      if sub == pair[0]:
        return mkTransformTuple(pair[1], false)
    return mkTransformTuple(sub, true)

proc containsSubtree(n: NimNode, sub: NimNode): bool =
  var q = @[n]
  while q.len > 0:
    let cur = q.pop
    if cur == sub:
      return true
    else:
      for child in cur:
        q.add(child)

  return false

# Ugly workaround for Nim bug:
# https://github.com/nim-lang/Nim/issues/4939
# TODO: remove this the second the bug is fixed
var cnt {.compileTime.} = 0
proc genIdent(
  s: string
): NimNode {.compileTime.} =
  inc cnt
  newIdentNode(s & "_classy_" & $cnt)

proc genSymParams(
  inParams: seq[NimNode],
  inPattern: NimNode
): tuple[params: seq[NimNode], pattern: NimNode] {.compileTime.} =
  ## Replace instance parameters with unique symbols
  var substitutions = newSeq[(NimNode, NimNode)]()

  result.params = inParams
  for i in 0..<len(result.params):
    let def = result.params[i]
    def.expectKind(nnkIdentDefs)
    let id = def[0]
    id.expectKind({nnkIdent, nnkSym})
    let newId = genIdent($id.ident & "_")
    result.params[i][0] = newId

    substitutions.add((id, newId))

  result.pattern = inPattern.replace(substitutions)

proc parseMember(
  tree: NimNode
): TypeclassMember {.compileTime.} =
  ## Parse typeclass member patterns in one of following forms:
  ## - ``(A: T1, B..) => [Constr[A, _, ...], Concrete, ...]``
  ## - ``(A: T1, B..) => Constr[A, _, ...]``
  ## - ``A => Constr[A, _, ...]``
  ## - ``Constr[_, ...]``
  ## - ``Concrete``
  let hasParams = tree.kind == nnkInfix and tree[0].eqIdent("=>")
  let (params0, pattern0) = (block:
    if hasParams:
      (parseMemberParams(tree[1]), tree[2])
    else:
      (@[], tree)
  )

  # Make sure parameters don't clash with anything in body
  let (params, patternsTree) = genSymParams(params0, pattern0)

  # Strip possible brackets around patterns
  let patternNodes = (block:
    if patternsTree.kind == nnkBracket:
      toSeq(patternsTree.children)
    else:
      @[patternsTree]
  )
  let patterns = patternNodes.map(n =>
    ConcretePattern(tree: n, arity: getArity(n))
  )

  TypeclassMember(
    params: params,
    patterns: patterns
  )

proc stripAccQuoted(n: NimNode): NimNode =
  case n.kind:
    of nnkAccQuoted: n[0]
    else: n

proc parseMemberOptions(
  args: seq[NimNode]
): MemberOptions =
  ## Parse following instance options:
  ## - ``skipping(foo)`` - skips ``foo`` definition
  ## - ``skipping(foo, bar)`` - skips ``foo`` and ``bar``
  ## - ``exporting(_)`` - export all symbols
  ## - ``exporting(foo, bar)`` - export ``foo`` and ``bar``

  result = MemberOptions(
    skipping: newSeq[NimNode](),
    exporting: ExportOptions(kind: eoNone)
  )
  for a in args:
    if a.kind == nnkCall and a[0].eqIdent("skipping"):
      # Don't check for duplicate symbols
      for i in 1..<a.len:
        a[i].expectKind({nnkIdent, nnkAccQuoted})
        result.skipping.add(stripAccQuoted(a[i]))

    elif a.kind == nnkCall and a[0].eqIdent("exporting"):
      if result.exporting.kind != eoNone:
        fail("Duplicate exporting clause", a)
      var acc = newSeq[NimNode]()
      for i in 1..<a.len:
        a[i].expectKind({nnkIdent, nnkAccQuoted})
        if a[i].eqIdent("_") and a.len > 2:
          # Can't mix wildcard with other exporting
          fail("Invalid exporting clause", a)
        acc.add(stripAccQuoted(a[i]))

      if acc.len == 1 and acc[0].eqIdent("_"):
        result.exporting = ExportOptions(kind: eoAll)
      else:
        result.exporting = ExportOptions(kind: eoSome, patterns: acc)

    else:
      fail("Invalid instance option", a)

proc parseTypeclassOptions(
  args: seq[NimNode]
): TypeclassOptions =
  result = TypeclassOptions(exported: false)
  for a in args:
    if a.eqIdent("exported"):
      if result.exported:
        fail("Duplicate exported clause", a)
      else:
        result.exported = true
    else:
      fail("Illegal typeclass option: ", a)

# Global for reuse in ``replaceInProcs``
proc mkBodyWorker(
  substs: seq[(AbstractPattern, ConcretePattern)]
): (n: NimNode, s: IntSet) -> GenTransformTuple[IntSet] =
  proc worker(sub: NimNode, substIndices0: IntSet): GenTransformTuple[IntSet] =
    var substIndices = substIndices0
    for ix, subst in substs:
      let (abstract, concrete) = subst
      if sub.matchesPattern(abstract):
        substIndices.incl(ix)

        proc processParam(n: NimNode): NimNode =
          let replaced = n.replaceInBody(substs, substIndices)
          substIndices = replaced.substIndices
          replaced.tree

        let newSub = concrete.instantiate(
          abstract,
          sub,
          processParam
        )
        return mkGenTransformTuple(newSub, false, substIndices)

    return mkGenTransformTuple(sub.copyNimTree, true, substIndices)

  worker

proc replaceInBody(
  tree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)],
  substIndices: IntSet
): tuple[tree: NimNode, substIndices: IntSet] =
  ## Replace ``substs`` in a tree.
  ## Add indices of any matching substs to `substIndices`
  transformDown[IntSet](
    tree,
    mkBodyWorker(substs),
    substIndices
  )

proc processProcParams(
  paramsTree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)]
): tuple[tree: NimNode, substIndices: IntSet] =
  paramsTree.expectKind(nnkFormalParams)
  var substIndices = initIntSet()
  proc processType(tree: NimNode, substIndices: var IntSet): NimNode =
    let res = tree.replaceInBody(substs, substIndices)
    substIndices = res.substIndices
    res.tree

  var res = newNimNode(nnkFormalParams)

  res.add(paramsTree[0].processType(substIndices))

  for i in 1..<paramsTree.len:
    let oldParam = paramsTree[i]
    var newParam = oldParam.copyNimTree
    newParam[1] = oldParam[1].processType(substIndices)
    res.add(newParam)

  (res, substIndices)

proc replaceInProcs(
  tree: NimNode,
  instanceParams: seq[NimNode],
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode {.compileTime.} =
  ## Traverse ``tree`` looking for top-level procs; inject ``instanceParams`` and
  ## replace ``substs`` in each one.
  ## Otherwise behaves the same as ``ReplaceInBody`` - replaces abstract
  ## patterns if encountered.

  proc worker(sub: NimNode): TransformTuple =
    case sub.kind
    of RoutineNodes:
      # This will be returned
      var res = sub

      # Replace in formal parameters
      let (newParams, substIndices0) =
        sub.params.processProcParams(substs)
      res.params = newParams

      # Replace in proc body
      let (newBody, substIndices1) =
        sub.body.replaceInBody(substs, substIndices0)
      res.body = newBody

      # Inject instance parameters to proc's generic param list
      var genParams = sub[2]
      expectKind(genParams, {nnkEmpty, nnkGenericParams})
      if genParams.kind == nnkEmpty and instanceParams.len > 0:
        genParams = newNimNode(nnkGenericParams)

      var instanceParamIndices = initIntSet()
      for i, param in instanceParams:
        for j, subst in substs:
          if j in substIndices1 and
             subst[1].tree.containsSubtree(param[0]):
            instanceParamIndices.incl(i)
            break

      for i in instanceParamIndices:
        genParams.add(instanceParams[i].copyNimTree)

      res[2] = genParams

      # Do not recurse - we already replaced everything using ``replaceInBody``
      mkTransformTuple(res, false)
    else:
      # Note that arguments of a replaced constructor are handled by
      # ``bodyWorker``, meaning any proc defs inside them don't get parameter
      # injection. This is probably the right thing to do, though.
      let substIndices = initIntSet()
      let genTup = mkBodyWorker(substs)(sub, substIndices)
      mkTransformTuple(genTup.newNode, true)

  transformDown(tree, worker)

proc removeSkippedProcs(
  tree: NimNode,
  skipping: seq[NimNode]
): NimNode {.compileTime.} =
  ## Traverse ``tree`` looking for top-level procs with names
  ## in ``skipping`` and remove their definitions.

  proc worker(sub: NimNode): TransformTuple =
    case sub.kind
    of RoutineNodes:
      let nameNode = stripAccQuoted(sub.name)
      if nameNode in skipping:
        mkTransformTuple(newEmptyNode(), false)
      else:
        mkTransformTuple(sub, false)
    else:
      mkTransformTuple(sub, true)

  transformDown(tree, worker)

proc addExportMarks(
  tree: NimNode,
  exporting: ExportOptions
): NimNode {.compileTime.} =
  proc contains(opts: ExportOptions, n: NimNode): bool =
    case opts.kind
    of eoNone: false
    of eoAll: true
    of eoSome: opts.patterns.contains(n)

  proc stripExportMark(n: NimNode): NimNode =
    if n.kind == nnkPostfix: n.basename else: n

  proc withExportMark(n: NimNode, mark: bool): NimNode =
    if mark: n.postfix("*") else: n

  proc worker(sub: NimNode): TransformTuple =
    case sub.kind
    of RoutineNodes:
      let exported = exporting.contains(sub.name)
      let res = sub.copyNimTree
      # Add or remove export mark
      # `name` proc strips quoting and postfixes - but we need them!
      res[0] = sub[0].stripExportMark.withExportMark(exported)
      # We're only processing top-level routines
      mkTransformTuple(res, false)

    of nnkIdentDefs:
      let name = sub[0].stripExportMark
      let exported = exporting.contains(name)
      let res = sub.copyNimTree
      res[0] = name.withExportMark(exported)
      # We're only processing top-level definitions
      # TODO: handle exports for object fields
      mkTransformTuple(res, false)

    else:
      mkTransformTuple(sub, true)

  transformDown(tree, worker)

proc instanceImpl(
  class: Typeclass,
  member: TypeclassMember,
  options: MemberOptions
): NimNode {.compileTime.} =

  if class.arity != member.arity:
    let msg = "Incorrect number of arguments for typeclass " & class.name
    fail(msg)

  let substs: seq[(AbstractPattern, ConcretePattern)] =
    class.patterns.zip(member.patterns)

  for s in substs:
    let (abstract, concrete) = s
    if abstract.arity != concrete.arity:
      let msg = "Type or constructor does not match typeclass parameter (" &
        $toStrLit(asTree(abstract)) & ")"
      fail(msg, concrete.tree)

  result = class.body.copyNimTree
  result = result.removeSkippedProcs(options.skipping)
  result = result.replaceInProcs(member.params, substs)
  result = result.addExportMarks(options.exporting)

# A hack to allow passing ``Typeclass`` values from the macro to
# defined variables
var tc {.compiletime.} : Typeclass

macro typeclass*(id, patternsTree: untyped, args: varargs[untyped]): typed =
  ## Define typeclass with name ``id``.
  ##
  ## This creates a compile-time variable with name ``id``.
  ##
  ## Call syntax:
  ##
  ## .. code-block:: nim
  ##
  ##   typeclass Class, [A[_, ..], B,...], exported:
  ##     <typeclass body>
  ##
  ## Typeclass can have zero or more parameters, each of which can be a type
  ## constructor with arity 1 and higher (like ``A`` in sample above), or be
  ## a concrete type (like ``B``). If a typeclass has exactly one parameter,
  ## the brackets around parameter list can be omitted.
  ##
  ## The ``exported`` option allows to export the typeclass from module.
  ## This marks corresponding variable with export postfix. Notice that in
  ## this case standard restrictions apply: the ``typeclass`` call should be
  ## in module's top scope.
  id.expectKind(nnkIdent)

  # Typeclass body goes last, before it - various options
  let argsSeq = toSeq(args)
  if argsSeq.len == 0:
    fail("Missing body for typeclass" & $id)
  let options = parseTypeclassOptions(argsSeq[0..^2])
  let body = argsSeq[argsSeq.len - 1]
  let patterns = parseAbstractPatterns(patternsTree)

  let idTree = if options.exported: id.postfix("*") else: id

  # Pass the value through ``tc``.
  # I do not know of a cleaner way to do this.
  tc = Typeclass(
    name: $id,
    patterns: patterns,
    body: body
  )
  let tcSym = bindSym("tc")
  quote do:
    let `idTree` {.compileTime.} = `tcSym`

macro instance*(
  class: static[Typeclass],
  argsTree: untyped,
  options: varargs[untyped]
): untyped =
  ## Instantiate typeclass ``class`` with given arguments
  ##
  ## Call syntax:
  ##
  ## .. code-block:: nim
  ##
  ##   instance Class, (K, L) => [AType[_, K,..], BType,...],
  ##     skipping(foo, bar),
  ##     exporting(_)
  ##
  ## ``instance`` does the following:
  ## 1. Replaces each of parameter forms in `typeclass` definition with
  ##    corresponding argument form (like ``AType`` in code example). Parameter
  ##    form list of ``typeclass`` and argument form lists of corresponding
  ##    `instance` calls must have matching length, and corresponding forms
  ##    should have the same arity.
  ## 2. Injects instance parameters (``K`` in the example) into top-level
  ##    routines in typeclass body.
  ## 3. Transforms the body according to options.
  ## 4. Executes the body.
  ##
  ## Instance `parameters` can have constraints in the same form as in a generic
  ## definition. If no instance parameters are present, the corresponding list
  ## can be omitted. If exactly one instance parameter is present (without
  ## constraints), the parenthesis around parameter list can be omitted.
  ##
  ## Instance `argument` forms are trees with zero or more nodes replaced with
  ## wildcards (``_``), the number of wildcards in a tree corresponding to
  ## the form arity. A form can include existing types, as well as instance
  ## `parameters`.
  ##
  ## Here are few valid parameter-argument combinations:
  ##
  ## .. code-block:: nim
  ##
  ##   []
  ##   int
  ##   Option[_]
  ##   [int, string]
  ##   K => Option[K]
  ##   (K: SomeInteger, L) => [(K, L, Option[_]), (L, int)]
  ##
  ## Supported instance options:
  ## 1. ``skipping(foo, bar...)`` - these definitions will be skipped.
  ## 2. ``exporting(foo, bar)`` - these generated definitions will have export
  ##    marker.
  ## 3. ``exporting(_)`` - all generated definitions will have export marker.

  var opts = newSeq[NimNode]()
  for o in options: opts.add(o)

  result = instanceImpl(class, parseMember(argsTree), parseMemberOptions(opts))

  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)
