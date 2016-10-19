import unittest, future, sequtils, options, ../classy

template shouldWork(body: untyped): untyped =
  when compiles(body):
    body
  else:
    check: compiles(body)

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
      typeclass Functor, F:
        # Can't use forward declarations for generics
        # proc fmap[A, B](fa: F[A], g: A -> B): F[B]

        proc `<$>`[A, B](g: A -> B, fa: F[A]): F[B] = fmap(fa, g)

      # Should allow type constructors
      proc fmap[A, B](fa: seq[A], g: A -> B): seq[B] = sequtils.map(fa, g)
      instance Functor, seq[_]

      check: ((x: int) => $x) <$> @[1, 2, 3] == @["1", "2", "3"]

  test "Monad":
    shouldWork:
      typeclass Monad, M:
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

      instance Monad, seq
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

suite "Specific features":
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
