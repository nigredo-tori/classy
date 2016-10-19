import macros, future
from sequtils import toSeq, applyIt

type
  Typeclass = object
    param: string
    body: NimNode

  TypeclassMember = object
    params: seq[NimNode]
    typeExpr: NimNode
    arity: int

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

proc replaceInBody(
  tree: var NimNode,
  param: string,
  member: TypeclassMember
) {.compileTime.}

proc getArity(tree: NimNode): int {.compileTime.} =
  # Just count all underscore idents
  if tree.eqIdent("_"):
    result = 1
  else:
    result = 0
    for child in tree:
      result.inc(getArity(child))

proc matchesConcrete(
  tree: NimNode, pattern: string
): bool {.compileTime.} =
  tree.eqIdent(pattern)

proc matchesConstructor(
  tree: NimNode, pattern: string
): bool {.compileTime.} =
  ## `M[A, B]` matches pattern `"M"`
  tree.kind == nnkBracketExpr and
    tree.len > 0 and
    tree[0].eqIdent(pattern)

proc instantiateConstructor(
  member: TypeclassMember, param: string, tree: NimNode
): NimNode {.compileTime.} =

  proc replaceUnderscores(
    tree: var NimNode, args: var seq[NimNode]
  ) =
    # Traverse `tree` and replace all underscore identifiers
    # with nodes from `args` in order. Mutates both `tree`
    # and `args` for ease of implementation.
    if tree.eqIdent("_"):
      tree = args[0]
      args.del(0)
    else:
      for i in 0..<tree.len:
        var child = tree[i]
        replaceUnderscores(child, args)
        tree[i] = child

  tree.expectKind(nnkBracketExpr)
  # First one is the constructor itself
  var args = toSeq(tree.children)
  args.del(0)

  # we can have recursion in type arguments!
  for i in 0..<args.len:
    var arg = args[i].copyNimTree
    replaceInBody(arg, param, member)
    args[i] = arg

  if args.len != member.arity:
    let msg = "Expected " & $member.arity & "type arguments, " &
      "got " & $args.len & "\L" &
      "In expression:\L " & $toStrLit(tree)
    error(msg)

  result = copyNimTree(member.typeExpr)
  for i in 0..<result.len:
    var child = result[i]
    replaceUnderscores(child, args)
    result[i] = child
  assert: args.len == 0

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

proc replace(n: NimNode, subst: seq[(NimNode, NimNode)]): NimNode {.compileTime.} =
  for pair in subst:
    if n == pair[0]: return pair[1].copyNimTree

  # Recurse
  result = n.copyNimNode
  for i in 0..<n.len:
    result.add(replace(n[i], subst))
  return result

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
  ## Parse typeclass member pattern in one of following forms:
  ## - `(A: T1, B..) => Expr[A, _, ...]`
  ## - `A => Expr[A, _, ...]`
  ## - `Expr[_, ...]`
  ## - `Expr`
  let hasParams = tree.kind == nnkInfix and tree[0].eqIdent("=>")
  let (params0, pattern0) = (block:
    if hasParams:
      (parseMemberParams(tree[1]), tree[2])
    else:
      (@[], tree)
  )

  # Make sure parameters don't clash with existing ones
  let (params, pattern) = genSymParams(params0, pattern0)

  TypeclassMember(
    params: params,
    typeExpr: pattern,
    arity: getArity(pattern)
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
        error("Duplicate exporting clause: " & $toStrLit(a))
      var acc = newSeq[NimNode]()
      for i in 1..<a.len:
        a[i].expectKind({nnkIdent, nnkAccQuoted})
        if a[i].eqIdent("_") and a.len > 2:
          # Can't mix wildcard with other exporting
          error("Invalid exporting clause: " & $toStrLit(a))
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
        error("Duplicate exported clause")
      else:
        result.exported = true
    else:
      error("Illegal typeclass option: " & $toStrLit(a))

proc replaceInBody(
  tree: var NimNode,
  param: string,
  member: TypeclassMember
) =
  ## Replace occurrences of `param` in a tree

  # concrete classes don't support argument injection
  let isConstructor = member.arity > 0
  if isConstructor and tree.matchesConstructor(param):
    tree = member.instantiateConstructor(param, tree)
  elif tree.matchesConcrete(param):
    # Member without parameters is injected as-is
    tree = member.typeExpr.copyNimTree
  else:
    # Recurse
    for i in 0..<tree.len:
      var sub = tree[i]
      replaceInBody(sub, param, member)
      tree[i] = sub

proc replaceInProcs(
  tree: var NimNode,
  param: string,
  member: TypeclassMember
) {.compileTime.} =
  ## Traverse `tree` looking for top-level procs, and replace
  ## `param` occurrences in each one with `member` instance.
  case tree.kind
  of RoutineNodes:
    # Inject method parameters to proc's generic param list
    var genParams = tree[2]
    expectKind(genParams, {nnkEmpty, nnkGenericParams})
    if genParams.kind == nnkEmpty and member.params.len > 0:
      genParams = newNimNode(nnkGenericParams)

    for p in member.params:
      genParams.add(p.copyNimTree)

    tree[2] = genParams

    # Replace in formal parameters
    var formalParams = tree.params
    replaceInBody(formalParams, param, member)
    tree.params = formalParams

    # Replace in proc body
    var procBody = tree.body
    replaceInBody(procBody, param, member)
    tree.body = procBody

  else:
    # Recurse
    for i in 0..<tree.len:
      var sub = tree[i]
      replaceInProcs(sub, param, member)
      tree[i] = sub

proc removeSkippedProcs(
  tree: var NimNode,
  skipping: seq[NimNode]
) {.compileTime.} =
  ## Traverse `tree` looking for top-level procs with names
  ## in `skipping` and remove their definitions.
  case tree.kind
  of RoutineNodes:
    let nameNode = tree.name
    if nameNode in skipping:
      tree = newEmptyNode()
  else:
    # Recurse
    for i in 0..<tree.len:
      var sub = tree[i]
      removeSkippedProcs(sub, skipping)
      tree[i] = sub

proc addExportMarks(
  tree: var NimNode,
  exporting: ExportOptions
) {.compileTime.} =
  proc contains(opts: ExportOptions, n: NimNode): bool =
    case opts.kind
    of eoNone: false
    of eoAll: true
    of eoSome: opts.patterns.contains(n)

  let matches = tree.kind in RoutineNodes and exporting.contains(tree.name)
  if matches:
    tree.name = tree.name.postfix("*")
  else:
    # Recurse
    for i in 0..<tree.len:
      var sub = tree[i]
      addExportMarks(sub, exporting)
      tree[i] = sub

proc instanceImpl(
  class: Typeclass,
  member: TypeclassMember,
  options: MemberOptions
): NimNode {.compileTime.} =
  result = class.body.copyNimTree
  result.removeSkippedProcs(options.skipping)
  result.replaceInProcs(class.param, member)
  result.addExportMarks(options.exporting)

# A hack to allow passing `Typeclass` values from the macro to
# defined variables
var tc {.compiletime.} : Typeclass

macro typeclass*(id, param: untyped, args: varargs[untyped]): typed =
  ## Define typeclass with name `id` and "signature" `param`.
  ##
  ## Warning: this creates a compile-time constant with name `id`.
  param.expectKind(nnkIdent)
  id.expectKind(nnkIdent)

  # Typeclass body goes last, before it - various options
  let argsSeq = toSeq(args)
  if argsSeq.len == 0:
    error("Missing body for typeclass " & $toStrLit(id))
  let options = parseTypeclassOptions(argsSeq[0..^2])
  let body = argsSeq[argsSeq.len - 1]

  let idTree = if options.exported: id.postfix("*") else: id

  # Pass the value through `tc`.
  # I do not know of a cleaner way to do this.
  tc = Typeclass(param: $param.ident, body: body)
  let tcSym = bindSym("tc")
  quote do:
    let `idTree` {.compileTime.} = `tcSym`

macro instance*(
  class: static[Typeclass],
  arg: untyped,
  options: varargs[untyped]
): untyped =
  var opts = newSeq[NimNode]()
  for o in options: opts.add(o)

  result = instanceImpl(class, parseMember(arg), parseMemberOptions(opts))
  # For debugging purposes
  when defined(classyDumpCode):
    echo toStrLit(result)
  when defined(classyDumpTree):
    echo treeRepr(result)
