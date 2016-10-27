import macros, future
from sequtils import apply, map, zip, toSeq, applyIt, allIt, mapIt

type
  AbstractPattern = object
    ## Type/pattern placeholder for typeclass declaration.
    ##
    ## Has either form `A` (placeholder for a concrete type) or `A[_,...]` (for
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

  Typeclass = object
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
  TransformTuple = object
    newNode: NimNode
    recurse: bool

proc mkTransformTuple(newNode: NimNode, recurse: bool): auto =
  TransformTuple(newNode: newNode, recurse: recurse)

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
): NimNode {.compileTime.} =
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
  ## Counts all underscore idents in `tree`
  if tree.eqIdent("_"):
    result = 1
  else:
    result = 0
    for child in tree:
      result.inc(getArity(child))

proc matchesPattern(
  tree: NimNode, pattern: AbstractPattern
): bool {.compileTime.} =
  ## Checks whether `tree` is an occurence of `pattern`
  ##
  ## Returns `true` if the patern matches, `false` otherwise.
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
    # Traverse `tree` and replace all underscore identifiers
    # with nodes from `args` in order.
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
  ## `A`, `(A, B)`, `(A: T1, B)` etc.

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
  ## Parses abstract pattern in forms `A` and `A[_,...]`
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
): TypeclassMember {.compileTime.} =
  ## Parse typeclass member patterns in one of following forms:
  ## - `(A: T1, B..) => [Constr[A, _, ...], Concrete, ...]`
  ## - `(A: T1, B..) => Constr[A, _, ...]`
  ## - `A => Constr[A, _, ...]`
  ## - `Constr[_, ...]`
  ## - `Concrete`
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
  ## - `skipping(foo)` - skips `foo` definition
  ## - `skipping(foo, bar)` - skips `foo` and `bar`

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

proc replaceInBody(
  tree: NimNode,
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode =
  ## Replace `substs` in a tree

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

  transformDown(tree, worker)

proc replaceInProcs(
  tree: NimNode,
  params: seq[NimNode],
  substs: seq[(AbstractPattern, ConcretePattern)]
): NimNode {.compileTime.} =
  ## Traverse `tree` looking for top-level procs; inject `params` and
  ## replace `substs` in each one.

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

      # Do not recurse - we already replaced everything with replaceInBody
      mkTransformTuple(res, false)
    else:
      mkTransformTuple(sub, true)

  transformDown(tree, worker)

proc removeSkippedProcs(
  tree: NimNode,
  skipping: seq[NimNode]
): NimNode {.compileTime.} =
  ## Traverse `tree` looking for top-level procs with names
  ## in `skipping` and remove their definitions.

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

# A hack to allow passing `Typeclass` values from the macro to
# defined variables
var tc {.compiletime.} : Typeclass

macro typeclass*(id, patternsTree: untyped, args: varargs[untyped]): typed =
  ## Define typeclass with name `id` and "signature" `param`.
  ##
  ## Warning: this creates a compile-time constant with name `id`.
  id.expectKind(nnkIdent)

  # Typeclass body goes last, before it - various options
  let argsSeq = toSeq(args)
  if argsSeq.len == 0:
    fail("Missing body for typeclass" & $id)
  let options = parseTypeclassOptions(argsSeq[0..^2])
  let body = argsSeq[argsSeq.len - 1]
  let patterns = parseAbstractPatterns(patternsTree)

  let idTree = if options.exported: id.postfix("*") else: id

  # Pass the value through `tc`.
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
  var opts = newSeq[NimNode]()
  for o in options: opts.add(o)

  result = instanceImpl(class, parseMember(argsTree), parseMemberOptions(opts))

  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)
