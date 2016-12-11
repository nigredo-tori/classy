import unittest, future, sequtils, options, ../classy

template shouldWork(body: untyped): untyped =
  when compiles(body):
    body
  else:
    check: compiles(body)

template shouldFail(body: untyped): untyped =
  block:
    check: not compiles(body)

suite "Typeclasses":
  test "Monoid":
    shouldWork:

      typeclass Monoid, M:
        # Can't use forward declarations for generics
        # proc mzero(t: typedesc[M]): M
        # proc mappend(a, b: M): M

        proc mconcat(ms: seq[M]): M =
          result = mzero(M)
          for m in ms:
            result = mappend(result, m)

      # Should work for one type
      proc mzero(t: typedesc[int]): int = 0
      proc mappend(a, b: int): int = a + b

      instance Monoid, int
      check: mconcat(@[1, 2, 3, 4]) == 10

      # Should allow more than one instance per typeclass
      proc mzero(t: typedesc[string]): string = ""
      proc mappend(a, b: string): string = a & b

      instance Monoid, string
      check: mconcat(@["foo", "bar"]) == "foobar"

      # Should allow parameterized instances
      proc mzero[A](t: typedesc[seq[A]]): seq[A] = @[]
      proc mappend[A](a, b: seq[A]): seq[A] = a & b

      instance Monoid, A => seq[A]
      check: mconcat(@[@[1, 2], @[3], @[4, 5]]) == @[1, 2, 3, 4, 5]

      # Should allow type constraints in parameters
      proc mzero[T: SomeNumber](t: typedesc[T]): T = 0
      proc mappend[T: SomeNumber](a, b: T): T = a + b

      instance Monoid, (T: SomeNumber) => T
      check: mconcat(@[0.5, 0.5]) == 1.0

  test "Functor":
    shouldWork:
      typeclass Functor, F[_]:
        # Can't use forward declarations for generics
        # proc fmap[A, B](fa: F[A], g: A -> B): F[B]

        proc `<$>`[A, B](g: A -> B, fa: F[A]): F[B] = fmap(fa, g)

      # Should allow type constructors
      proc fmap[A, B](fa: seq[A], g: A -> B): seq[B] = sequtils.map(fa, g)
      instance Functor, seq[_]

      check: ((x: int) => $x) <$> @[1, 2, 3] == @["1", "2", "3"]

  test "Monad":
    shouldWork:
      typeclass Monad, M[_]:
        # Can't use forward declarations for generics
        # proc point[A](t: typedesc[M[A]], v: A): M[A]
        # proc flatMap[A, B](ma: M[A], f: A -> M[B]): M[B]

        proc join[A](mma: M[M[A]]): M[A] =
          mma.flatMap((ma: M[A]) => ma)

      # Should allow instances for type constructors without patterns
      proc flatMap[A, B](ma: seq[A], f: A -> seq[B]): seq[B] =
        result = newSeq[B]()
        for a in ma:
          result.add(f(a))

      instance Monad, seq[_]
      check: join(@[@[1, 2], @[3]]) == @[1, 2, 3]

      # Should allow mixing parameters with concrete types and wildcards
      # This also checks that macro correctly handles recursion in arguments
      proc flatMap[N, S, A, B](ma: (N, S, A), f: A -> (N, S, B)): (N, S, B) =
        let (n1, s1, a) = ma
        let (n2, s2, b) = f(a)
        (n1 + n2, s1 & s2, b)

      # Notice we don't reuse parameter names here - this is not yet supported
      instance Monad, N => (N, string, _)
      check: join((1, "foo", (2, "bar", 0.5))) == (3, "foobar", 0.5)

  test "Bifunctor":
    shouldWork:
      # Should allow multi-parameter patterns
      typeclass Bifunctor, F[_, _]:
        # proc bimap[A, B, C, D](f: F[A, B], g: A -> C, h: B -> D): F[C, D]
        proc first[A, B, C](f: F[A, B], g: A -> C): F[C, B] =
          f.bimap(g, (b: B) => b)
        proc second[A, B, C](f: F[A, B], h: B -> C): F[A, C] =
          f.bimap((a: A) => a, h)

      proc bimap[A, B, C, D](f: (A, B), g: A -> C, h: B -> D): (C, D) =
        (g(f[0]), h(f[1]))

      instance Bifunctor, (_, _)
      let t = (0.5.float, '2')
        .first(x => $x)
        .second(y => ord(y).int - ord('0'))
      check: t == ("0.5", 2)

suite "Multi-parameter typeclasses":
  test "Should support multi-parameter typeclasses":
    shouldWork:
      typeclass Conversion, [A, B]:
        #proc to(a: A, tb: typedesc[B]): B
        proc mapTo(sa: seq[A], tb: typedesc[B]): seq[B] =
          sa.map(a => a.to(B))

      proc to(x: int, tb: typedesc[string]): string = $x
      instance Conversion, [int, string]
      check: @[1, 2, 3].mapTo(string) == @["1", "2", "3"]

  test "Should check typeclass arity when instantiating":
    shouldWork:
      # Also checks few related features
      typeclass NoArgs, []: discard
      shouldWork: instance NoArgs, []
      shouldFail: instance NoArgs, int
      shouldFail: instance NoArgs, [int]

      typeclass OneArg1, A: discard
      shouldFail: instance OneArg1, []
      shouldWork: instance OneArg1, int
      shouldWork: instance OneArg1, [int]
      shouldFail: instance OneArg1, [int, string]

      typeclass OneArg2, [A]: discard
      shouldFail: instance OneArg2, []
      shouldWork: instance OneArg2, int
      shouldWork: instance OneArg2, [int]
      shouldFail: instance OneArg2, [int, string]

      typeclass TwoArgs, [A, B]: discard
      shouldFail: instance TwoArgs, int
      shouldWork: instance TwoArgs, [int, string]
      shouldFail: instance TwoArgs, [int, string, float]

suite "isTypeclassInstance":
  test "Should work for simple case":
    shouldWork:
      typeclass Foo, F: discard
      instance Foo, int
      instance Foo, float

      check: isTypeclassInstance(int, Foo)
      check: isTypeclassInstance(float, Foo)
      check: not isTypeclassInstance(string, Foo)
      check: not isTypeclassInstance(bool, Foo)

  test "Shouldn't confuse typeclasses in simple case":
    typeclass Foo, F: discard
    typeclass Bar, F: discard
    instance Foo, int

    check: isTypeclassInstance(int, Foo)
    check: not isTypeclassInstance(int, Bar)

  test "Should work for simple type constructors":
    shouldWork:
      type A[T] = object
      typeclass Foo, F[_]: discard
      instance Foo, A[_]

      check: isTypeclassInstance(A[_], Foo)
      check: not isTypeclassInstance(Option[_], Foo)

  test "Should work for more complex constructors":
    shouldWork:
      type A[U, V] = object
      type B[U, V] = object

      typeclass Foo, F[_, _]: discard
      instance Foo, A[_, _]

      check: isTypeclassInstance(A[_, _], Foo)
      check: not isTypeclassInstance(B[_,_], Foo)

      # Shouldn't confuse parameters
      type RevA[V, U] = A[U, V]
      type RevRevA[U, V] = RevA[V, U] # same as A

      static: echo "before"      
      check: not isTypeclassInstance(RevA[_, _], Foo)
      static: echo "after"
      check: isTypeclassInstance(RevRevA[_, _], Foo)

  test "Should work for partial application":
    shouldWork:
      type A[U, V] = object
      typeclass Foo, F[_]: discard
      instance Foo, A[int, _]

      check: isTypeclassInstance(A[int, _], Foo)
      check: not isTypeclassInstance(A[string, _], Foo)

  test "Should work (kind of) for instance parameters":
    shouldWork:
      type A[U, V] = object
      typeclass Foo, F: discard
      instance Foo, (I: SomeInteger) => A[I, I]

      check: isTypeclassInstance((I: SomeInteger) => A[I, I], Foo)

  test "Should not confuse instance parameters with placeholders":
    shouldWork:
      type A[U, V] = object
      typeclass Foo, F[_]: discard
      instance Foo, I => A[I, _]

      check: isTypeclassInstance(I => A[I, _], Foo)
      check: not isTypeclassInstance(I => A[_, I], Foo)
      check: not isTypeclassInstance(I => A[I, I], Foo)

  test "Should correctly resolve instances with more general parameters":
    #shouldWork:
      type A[U, V, W] = object
      typeclass Foo, F: discard

      instance Foo, (X, Y) => A[X, Y, Y]

      check: isTypeclassInstance((X, Y) => A[X, Y, Y], Foo)
      check: isTypeclassInstance(Z => A[Z, Z, Z], Foo)
      check: not isTypeclassInstance((X, Y) => A[X, X, Y], Foo)

suite "Constraints":
  test "Should work for the simple case":
    shouldWork:
      typeclass Foo, F: discard
      typeclass Bar, (B: Foo) => B: discard

      instance Foo, int

      shouldWork:
        instance Bar, int

      shouldFail:
        instance Bar, string

suite "Miscellaneous features":
  test "Skipping definitions":
    shouldWork:
      typeclass Some, S:
        proc foo: S = 1
        proc bar: S = 2
        proc `$%^`: S = 3

      block:
        instance Some, int,
             skipping(bar)

        check: declared(foo)
        check: not declared(bar)
        check: declared(`$%^`)

      block:
        instance Some, int,
             skipping(foo, bar, `$%^`)

        check: not declared(foo)
        check: not declared(bar)
        check: not declared(`$%^`)

  test "Template support":
    shouldWork:
      typeclass WithInverse, F:
        template inverse(f: F): F = -f
      instance WithInverse, int
      check: inverse(123) == -123
      check: not compiles(inverse(1.0))

  test "Member parameters should not cause collision":
    shouldWork:
      typeclass Some, S:
        proc foo[A](a: A, s: S): string =
          $a & "," & $s

      instance Some, A => Option[A]
      assert: foo(123, some("foo")) == "123,Some(foo)"

  test "Should fail for constructor without arguments in body":
    shouldFail:
      typeclass Bad, B[_]:
        proc foo(x: B) = discard
      instance Bad, seq[_]

  test "Should properly inject outside proc definitions":
    shouldWork:
      typeclass Foo, F:
        let fooVal: F = 0

      instance Foo, int
      assert: fooVal == 0
