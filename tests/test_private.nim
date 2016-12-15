include ../classy
import unittest

suite "sampleMatches":
  test "should work for atomic types":
    type
      A = object
      B = object

    check: sampleMatches(int, int)
    check: sampleMatches(string, string)
    check: not sampleMatches(int, string)
    check: not sampleMatches(int, BiggestInt)
    check: not sampleMatches(BiggestInt, int)
    check: sampleMatches(A, A)
    check: not sampleMatches(A, B)
    check: not sampleMatches(int, A)
    check: not sampleMatches(A, int)

  test "should work for generics/builtin generic-like types":
    type
      A = object
      B[T] = object
      C[T] = object
      D[X, Y] = object

    check: sampleMatches(B[int], B[int])
    check: not sampleMatches(B[int], C[int])
    check: not sampleMatches(B[int], B[string])
    check: sampleMatches(B[D[int, C[string]]], B[D[int, C[string]]])
    check: not sampleMatches(B[D[int, C[string]]], B[D[int, C[float]]])

    check: sampleMatches(seq[char], seq[char])
    check: not sampleMatches(seq[int], seq[char])
    check: not sampleMatches(seq[char], set[char])

  test "should work for placeholder":
    # Only matches itself
    type
      Foo[A] = object
      Bar[n: static[int]] = object

    check: sampleMatches(
      Placeholder[0],
      Placeholder[0],
    )
    check: not sampleMatches(
      Placeholder[1],
      Placeholder[0],
    )
    check: not sampleMatches(
      int,
      Placeholder[0],
    )
    check: not sampleMatches(
      seq[int],
      Placeholder[0]
    )
    check: not sampleMatches(
      Foo[int],
      Placeholder[0]
    )
    check: not sampleMatches(
      Bar[0],
      Placeholder[0]
    )

  test "should work for an unbound parameter":
    # Matches anything that doesn't have a placeholder inside
    type
      Foo[A] = object
      Bar[n: static[int]] = object

    check: sampleMatches(
      int,
      Parameter[0],
    )
    check: sampleMatches(
      string,
      Parameter[0],
    )
    check: sampleMatches(
      seq[int],
      Parameter[0],
    )
    check: sampleMatches(
      Foo[int],
      Parameter[0],
    )
    check: sampleMatches(
      Bar[0],
      Parameter[0],
    )
    check: sampleMatches(
      Parameter[0],
      Parameter[0],
    )
    check: sampleMatches(
      Parameter[1],
      Parameter[0],
    )
    check: not sampleMatches(
      Placeholder[0],
      Parameter[0],
    )
    check: not sampleMatches(
      Foo[Placeholder[0]],
      Parameter[0],
    )
    check: not sampleMatches(
      Foo[Foo[Placeholder[0]]],
      Parameter[0],
    )
    check: sampleMatches(
      Foo[Foo[Parameter[123]]],
      Parameter[0],
    )

  test "should work for a bound parameter":
    # Matches only what was previously bound
    type
      Two[A, B] = object
      Foo[A] = object

    check: sampleMatches(
      Two[int, int],
      Two[Parameter[0], Parameter[0]]
    )
    check: not sampleMatches(
      Two[int, float],
      Two[Parameter[0], Parameter[0]]
    )
    check: sampleMatches(
      Two[Foo[Two[Parameter[123], int]], Foo[Two[Parameter[123], int]]],
      Two[Parameter[0], Parameter[0]]
    )
    check: not sampleMatches(
      Two[Foo[Two[Parameter[321], int]], Foo[Two[Parameter[123], int]]],
      Two[Parameter[0], Parameter[0]]
    )
    check: not sampleMatches(
      Two[Foo[Two[Parameter[123], int]], Foo[Two[Parameter[123], float]]],
      Two[Parameter[0], Parameter[0]]
    )

  test "should not mix up parameters":
    type
      Two[A, B] = object
      Three[A, B, C] = object

    check: sampleMatches(
      Two[int, float],
      Two[Parameter[1], Parameter[0]]
    )

    check: sampleMatches(
      Three[int, float, int],
      Three[Parameter[0], Parameter[1], Parameter[0]]
    )

    check: not sampleMatches(
      Three[int, float, float],
      Three[Parameter[0], Parameter[1], Parameter[0]]
    )

  test "should work for distinct types":
    type
      A = object
      B[X] = object
      C[X, Y] = object

      ADist = distinct A
      ADist2 = distinct A
      BDist[X] = distinct B[X]
      BIntDist = distinct B[int]
      CDist[X, Y] = distinct C[X, Y]

    check: not sampleMatches(ADist, A)
    check: not sampleMatches(A, ADist)
    check: sampleMatches(ADist, ADist)
    check: not sampleMatches(ADist, ADist2)

    check: not sampleMatches(BDist[int], B[int])
    check: not sampleMatches(B[int], BDist[int])
    check: sampleMatches(BDist[int], BDist[int])
    check: not sampleMatches(BIntDist, B[int])
    check: not sampleMatches(B[int], BIntDist)

    check: not sampleMatches(CDist[int, string], C[int, string])
    check: not sampleMatches(C[int, string], CDist[int, string])
    check: sampleMatches(CDist[int, string], CDist[int, string])
    check: not sampleMatches(CDist[int, string], CDist[int, int])
    check: not sampleMatches(CDist[string, int], CDist[int, int])

  test "should work for aliases":
    type
      A = object
      B[X] = object
      C[X, Y] = object

      AAlias = A
      BAlias[X] = B[X]
      BIntAlias = B[int]
      CAlias[X, Y] = C[X, Y]
      CIntAlias[Y] = C[int, Y]
      CRevAlias[Y, X] = C[X, Y]
      CDoubleAlias[X] = C[X, X]

    check: sampleMatches(A, AAlias)
    check: sampleMatches(AAlias, A)

    check: sampleMatches(B[int], BAlias[int])
    check: sampleMatches(BAlias[int], B[int])
    check: not sampleMatches(B[string], BAlias[int])
    check: not sampleMatches(BAlias[int], B[string])

    check: sampleMatches(BAlias[BAlias[int]], B[B[int]])
    check: sampleMatches(B[B[int]], BAlias[BAlias[int]])
    check: not sampleMatches(BAlias[BAlias[int]], B[B[string]])
    check: not sampleMatches(B[B[string]], BAlias[BAlias[int]])

    check: sampleMatches(CAlias[int, string], C[int, string])
    check: sampleMatches(C[int, string], CAlias[int, string])
    check: not sampleMatches(CAlias[int, string], C[int, int])
    check: not sampleMatches(CAlias[int, int], CAlias[int, string])

    check: sampleMatches(CIntAlias[string], C[int, string])
    check: sampleMatches(C[int, string], CIntAlias[string])
    check: not sampleMatches(CIntAlias[string], C[int, int])
    check: not sampleMatches(C[int, int], CIntAlias[string])
    check: not sampleMatches(CIntAlias[string], C[string, string])
    check: not sampleMatches(C[string, string], CIntAlias[string])

    check: sampleMatches(CRevAlias[int, string], C[string, int])
    check: sampleMatches(C[string, int], CRevAlias[int, string])
    check: not sampleMatches(CRevAlias[int, string], C[int, string])

    check: sampleMatches(CDoubleAlias[int], C[int, int])
    check: not sampleMatches(CDoubleAlias[int], C[string, string])
    check: not sampleMatches(CDoubleAlias[int], C[int, string])
    check: not sampleMatches(CDoubleAlias[int], C[string, int])

    check: sampleMatches(C[int, int], CDoubleAlias[int])
    check: not sampleMatches(C[string, string], CDoubleAlias[int])
    check: not sampleMatches(C[int, string], CDoubleAlias[int])
    check: not sampleMatches(C[string, int], CDoubleAlias[int])

  test "Should work for aliases with unused parameters":
    # These are handled differently by `getTypeInst` for some reason
    # TODO: Can't properly handle this case at the moment:
    # https://github.com/nim-lang/Nim/issues/5121
    type
      A = object
      AAlias = A
      AConstAlias[X] = A

    check: sampleMatches(AConstAlias[int], A)
    check: sampleMatches(A, AConstAlias[int])
    check: sampleMatches(AAlias, AConstAlias[int])
    check: sampleMatches(AConstAlias[string], AAlias)

  test "Aliases don't block recursion in placeholder check":
    # TODO: Can't properly handle this case at the moment:
    # https://github.com/nim-lang/Nim/issues/5121
    type
      A[X] = X
      B = Placeholder[0]
      C = int

    check: sampleMatches(
      A[C],
      Parameter[0],
    )

    check: not sampleMatches(
      B,
      Parameter[0],
    )

    check: not sampleMatches(
      A[Placeholder[0]],
      Parameter[0],
    )

    check: not sampleMatches(
      A[B],
      Parameter[0],
    )
