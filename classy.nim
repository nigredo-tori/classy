import macros, future
from sequtils import apply, map, zip, toSeq, applyIt, allIt, mapIt, concat, filterIt, foldl

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
## Notice that we ``fmap`` is not part of the typeclass. At the moment forward
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

  Constraint = object
    # An untyped pattern, e.g. ``F[int, _, string]
    # Can include typeclass parameters.
    # Note that, since this is untyped, any concrete symbols here are resolved
    # in instantiation time!!!
    form: NimNode
    # It's bothersome to pull static typeclass objects out of untyped tree.
    # For now a looked-up symbol is plenty.
    class: Typeclass

  Typeclass = ref object
    # Only here for better error messaging.
    # Do not use for membership checks and such!
    name: string
    symbol: NimSym
    patterns: seq[AbstractPattern]
    constraints: seq[Constraint]
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
  TransformTuple = object
    newNode: NimNode
    recurse: bool

  InstancePair = object
    patternSamples: seq[NimNode]
    class: Typeclass

# We can't store patterns for instances as untyped trees - this would break
# whenever time two scopes would disagree on something.
# We can't simply store them as typed trees either - this doesn't
# work for type constructors.
# So we prepare them as follows:
# 1. Take a pattern
# 2. Replace all parameters with unique types from parameterTypes in order
# 3. Replace all placeholder entries with unique types from placeholderTypes
#   in order.
# 4. Pass the result through semantic phase to resolve all types
# 5. Done.
# This way we get a concrete type to store, from which we can reconstruct
# the initial pattern (except for constraints on parameters).

# These types are only used here. So there's no way they collide with
# some other type (unless someone gets into this library's internals).

type Placeholder[n: static[int]] = object
type Parameter[n: static[int]] = object

proc parseMember(
  tree: NimNode
): TypeclassMember {.compileTime.}

proc transformDown(
  tree: NimNode,
  f: NimNode -> TransformTuple
): NimNode {.compileTime.}

proc mkTransformTuple(newNode: NimNode, recurse: bool): auto =
  TransformTuple(newNode: newNode, recurse: recurse)

proc `==`(a, b: Typeclass): bool =
  # I can't seem to find a direct way to compare two symbols
  # TODO: use some artificial typeclass ID fields?
  var na = newNimNode(nnkSym)
  na.symbol = a.symbol
  var nb = newNimNode(nnkSym)
  nb.symbol = b.symbol

  na == nb

template exportClassyInstances* =
  ## Place this at the beginning of the module, to export all
  ## instances, declared in module scope.
  ##
  ## Note that this doesn't export generated symbols for each
  ## instance - only the fact that an instance exists.
  var classyInstances* {.compileTime, inject.} = newSeq[`InstancePair`]()

template defineClassyInstances =
  when not definedInScope(classyInstances):
    # We don't declare exported instance list implicitly!
    var classyInstances {.compileTime, inject.} = newSeq[`InstancePair`]()

macro injectConstraint(
  into: static[Typeclass],
  form: untyped,
  class: static[Typeclass]
): typed =
  let c = Constraint(
    form: form,
    class: class
  )

  into.constraints.add(c)

macro injectSymbol(
  into: static[Typeclass],
  symTree: typed
): typed =
  into.symbol = symTree.symbol

proc makeSamples(
  instanceSignature: NimNode
): seq[NimNode] =
  ## Parse instance signature and construct samples for concrete patterns

  proc replaceParams(n: NimNode, params: seq[NimNode]): TransformTuple =
    for i, p in params:
      if n == p[0]:
        let res = newTree(
          nnkBracketExpr,
          bindSym("Parameter", brClosed),
          newIntLitNode(i)
        )
        return mkTransformTuple(
          res,
          false
        )
    return mkTransformTuple(n, true)

  proc replacePlaceholders(n: NimNode): NimNode =
    var i = 0
    proc worker(n: NimNode): TransformTuple =
      if n.eqIdent("_"):
        let res = newTree(
          nnkBracketExpr,
          bindSym("Placeholder", brClosed),
          newIntLitNode(i)
        )
        inc i
        return mkTransformTuple(
          res,
          false
        )
      return mkTransformTuple(n, true)

    return n.transformDown(worker)

  let instance = parseMember(instanceSignature)
  var samples = newSeq[NimNode]()

  for pattern in instance.patterns:
    let sample = pattern.tree
      .transformDown(n => replaceParams(n, instance.params))
      .replacePlaceholders
    samples.add(sample)

  samples

proc makeInstancePair(
  instanceSignature: NimNode,
  class: Typeclass
): InstancePair {.compileTime.} =
  InstancePair(
    patternSamples: makeSamples(instanceSignature),
    class: class
  )

var ip {.compileTime.}: InstancePair
macro injectInstancePair(
  instances: untyped,
  pattern: untyped,
  class: static[Typeclass]
): typed =
  ip = makeInstancePair(pattern, class)
  let ipSym = bindSym("ip", brClosed)
  quote do:
    static:
      # Always inject into closest instance list
      `instances`.add(`ipSym`)

template fail(msg: string, n: NimNode = nil) =
  let errMsg = if n != nil: msg & ": " & $toStrLit(n) else: msg
  error(errMsg, n)

proc arity(x: Typeclass): Natural {.compileTime.} =
  x.patterns.len

proc arity(x: TypeclassMember): Natural {.compileTime.} =
  x.patterns.len

proc replaceInBody(
  tree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode {.compileTime.}

proc transformDown(
  tree: NimNode,
  f: NimNode -> TransformTuple
): NimNode =
  let tup = f(tree.copyNimTree)

  result = tup.newNode
  if tup.recurse:
    for i in 0..<result.len:
      result[i] = transformDown(result[i], f)

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

proc splitConstraintsTree(
  constraintsTree: NimNode
): seq[NimNode] {.compileTime.} =
  ## Accepts constraints with syntax ``(A: TA, B: TB ...)`` or ``A: TA``.
  ## Here ``A``, ``B`` are forms, and ``TA``, ``TB`` are existing typeclasses.
  ## Returns AST ``A: TA`` for each pair.
  if constraintsTree.kind == nnkPar:
    # Parenthesized constraint list
    toSeq(constraintsTree.children)
  else:
    # A lone constraint
    @[constraintsTree]

proc makeInjectConstraintAst(
  typeclassId: NimNode,
  constraintTree: NimNode
): NimNode {.compileTime.} =
  if constraintTree.kind != nnkExprColonExpr:
    error "Invalid constraint syntax", constraintTree
  constraintTree.expectLen(2)

  let form = constraintTree[0]
  let class = constraintTree[1]
  let injectConstraint = bindSym("injectConstraint", brClosed)

  # We need another macro call here since we can't simply look up an ident:
  # https://github.com/nim-lang/Nim/issues/3559 .
  # We're lucky we don't have to generate macro definitions!
  (quote do:
    `injectConstraint`(`typeclassId`, `form`, `class`)
  )[0]

proc makeInjectInstanceAst(
  pattern: NimNode,
  typeclassId: NimSym
): NimNode {.compileTime.} =
  # TODO: replace classyInstance with a unique ident? What about imports, then?
  # TODO: don't export instances if the instance definition is not being exported
  let injectInstancePair = bindSym("injectInstancePair")
  let defineClassyInstances = bindSym("defineClassyInstances")
  let InstancePair = bindSym("InstancePair")
  quote do:
    # We want our instances to respect scopes
    `defineClassyInstances`
    static:
      `injectInstancePair`(
        classyInstances,
        `pattern`,
        `typeclassId`
      )

proc parseTypeclassSignature(
  tree: NimNode
): tuple[
  constraintTrees: seq[NimNode],
  patterns: seq[AbstractPattern]
] {.compileTime.} =
  if tree.kind == nnkInfix and tree[0].eqIdent("=>"):
    (splitConstraintsTree(tree[1]), parseAbstractPatterns(tree[2]))
  else:
    # This
    # TODO: something cleaner?
    (@[], parseAbstractPatterns(tree))

proc replace(n: NimNode, subst: seq[(NimNode, NimNode)]): NimNode {.compileTime.} =
  transformDown(n) do (sub: NimNode) -> auto:
    for pair in subst:
      if sub == pair[0]:
        return mkTransformTuple(pair[1], false)
    return mkTransformTuple(sub, true)

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
  ## Replaces member parameters with unique symbols
  var substitutions = newSeq[(NimNode, NimNode)]()

  result.params = inParams
  for i in 0..<len(result.params):
    let def = result.params[i]
    def.expectKind(nnkIdentDefs)
    let id = def[0]
    let newId = genIdent($id.ident & "_")
    result.params[i][0] = newId

    substitutions.add((id, newId))

  result.pattern = inPattern.replace(substitutions)

proc parseMember(
  tree: NimNode
): TypeclassMember =
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
        result.skipping.add(a[i])

    if a.kind == nnkCall and a[0].eqIdent("exporting"):
      if result.exporting.kind != eoNone:
        fail("Duplicate exporting clause", a)
      var acc = newSeq[NimNode]()
      for i in 1..<a.len:
        a[i].expectKind({nnkIdent, nnkAccQuoted})
        if a[i].eqIdent("_") and a.len > 2:
          # Can't mix wildcard with other exporting
          fail("Invalid exporting clause", a)
        acc.add(a[i])

      if acc.len == 1 and acc[0].eqIdent("_"):
        result.exporting = ExportOptions(kind: eoAll)
      else:
        result.exporting = ExportOptions(kind: eoSome, patterns: acc)

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
proc mkBodyWorker(substs: seq[(AbstractPattern, ConcretePattern)]): auto =
  proc worker(sub: NimNode): TransformTuple =
    for subst in substs:
      let (abstract, concrete) = subst
      if sub.matchesPattern(abstract):
        let newSub = concrete.instantiate(
          abstract, sub,
          processParam = ((n: NimNode) => n.replaceInBody(substs))
        )
        return mkTransformTuple(newSub, false)

    return mkTransformTuple(sub.copyNimTree, true)

  worker

proc replaceInBody(
  tree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode =
  ## Replace ``substs`` in a tree
  transformDown(tree, mkBodyWorker(substs))

proc replaceInProcs(
  tree: NimNode,
  params: seq[NimNode],
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode {.compileTime.} =
  ## Traverse ``tree`` looking for top-level procs; inject ``params`` and
  ## replace ``substs`` in each one.
  ## Otherwise behaves the same as ``ReplaceInBody`` - replaces abstract
  ## patterns if encountered.

  # Fallback worker function
  let bodyWorker = mkBodyWorker(substs)

  proc worker(sub: NimNode): TransformTuple =
    case sub.kind
    of RoutineNodes:
      # Inject method parameters to proc's generic param list
      # This will be returned
      var res = sub

      var genParams = sub[2]
      expectKind(genParams, {nnkEmpty, nnkGenericParams})
      if genParams.kind == nnkEmpty and params.len > 0:
        genParams = newNimNode(nnkGenericParams)

      for p in params:
        genParams.add(p.copyNimTree)

      res[2] = genParams

      # Replace in formal parameters
      let formalParams = sub.params
      res.params = formalParams.replaceInBody(substs)

      # Replace in proc body
      let procBody = sub.body
      res.body = procBody.replaceInBody(substs)

      # Do not recurse - we already replaced everything using ``replaceInBody``
      mkTransformTuple(res, false)
    else:
      # Notice that arguments of a replaced constructor are handled by
      # ``bodyWorker``, meaning any proc defs inside them don't get parameter
      # injection. This is probably the right thing to do, though.
      bodyWorker(sub)

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
      let nameNode = sub.name
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

  proc worker(sub: NimNode): TransformTuple =
    let matches = sub.kind in RoutineNodes and exporting.contains(sub.name)
    if matches:
      let res = sub.copyNimTree
      res.name = sub.name.postfix("*")
      mkTransformTuple(res, false)
    else:
      mkTransformTuple(sub, true)

  transformDown(tree, worker)

proc instanceImpl(
  class: Typeclass,
  rawPattern: NimNode,
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

  result.add(makeInjectInstanceAst(rawPattern, class.symbol))

macro sampleMatches(a, b: typedesc): untyped =
  let aType = a.getTypeInst[1]
  let bType = b.getTypeInst[1]
  let res = aType.sameType(bType)
  newLit(res)

proc samplesMatch(
  xs, ys: seq[NimNode],
  className: string,
  concretePattern: NimNode
): NimNode =
  ## Costruct an expression that evalues to ``true`` iff ``xs`` matches ``ys``.
  # TODO: properly check arity/shape
  if xs.len != ys.len:
    error(
      "Incorrect arity for typeclass " & className,
      concretePattern
    )

  let sampleMatches = bindSym"sampleMatches"
  let boolAnd = bindSym"and"

  # TODO: more precise matching
  # e.g. this fails if existing instance is more general
  xs.zip(ys)
    .mapIt(newCall(`sampleMatches`, it.a, it.b))
    .foldl(newCall(boolAnd, a, b), newLit(true))

macro isTypeclassInstanceImpl(
  concretePattern: untyped,
  class: static[Typeclass],
  instances: static[seq[InstancePair]]
): untyped =
  ## Costruct an expression that statically evalues to ``true`` iff
  ##``concretePattern`` has an instance of ``class``.
  ## For now matching is defined as equality.
  let samples = makeSamples(concretePattern)

  let boolOr = bindSym"or"

  instances.filterIt(it.class == class)
    .mapIt(samples.samplesMatch(
      it.patternSamples,
      class.name, concretePattern
    )).foldl(newCall(boolOr, a, b), newLit(false))

macro isTypeclassInstance*(
  concretePattern: untyped,
  class: static[Typeclass]
): untyped =
  ## Receives concrete pattern (type or type constructor with the same syntax as
  ## in ``instance``), and a typeclass.
  ## Returns ``true`` if the pattern is an instance of the typeclass.

  let getInstances = genSym(nskMacro, "getInstances")
  let concat = bindSym("concat", brClosed)
  let isTypeclassInstanceImpl = bindSym("isTypeclassInstanceImpl")

  let classSym = class.symbol
  let treeRepr = bindSym("treeRepr")

  result = quote do:
    macro `getInstances`(): untyped =
      # Following is a simple fold, made more verbose due to
      # scoping and typing considerations
      let choice = bindSym("classyInstances", brForceOpen)
      if choice.len == 0:
        return (
          quote do:
            @[]
        )[0]

      var res: NimNode = nil

      for i in 0..<choice.len:
        if res == nil:
          res = choice[i]
        else:
          res = newCall(
            ident"&",
            res,
            choice[i]
          )

      res

    `isTypeclassInstanceImpl`(
      `concretePattern`,
      `classSym`,
      `getInstances`()
    )

  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)

# A hack to allow passing ``Typeclass`` values from the macro to
# created compile-time variables.
# ``quote`` does weirdest things here.
var tc {.compiletime.} : Typeclass

macro typeclass*(id, signatureTree: untyped, args: varargs[untyped]): typed =
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
  let (constraintTrees, patterns) = parseTypeclassSignature(signatureTree)

  let idTree = if options.exported: id.postfix("*") else: id
  let idTreeCopy = idTree.copyNimTree

  # Pass the value through ``tc``.
  # I do not know of a cleaner way to do this.
  tc = Typeclass(
    name: $id,
    patterns: patterns,
    constraints: newSeq[Constraint](),
    body: body
  )
  let tcSym = bindSym("tc")
  let injectSymbol = bindSym("injectSymbol")
  let symSym = bindSym("symbol")

  result = quote do:
    let `idTree` {.compileTime.} = `tcSym`
    `injectSymbol`(`idTree`, `idTreeCopy`)

  for n in constraintTrees:
    let inject = makeInjectConstraintAst(idTree, n)
    result.add(inject)

  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)

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

  result = instanceImpl(
    class,
    argsTree,
    parseMember(argsTree),
    parseMemberOptions(opts)
  )

  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)
