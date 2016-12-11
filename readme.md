# Classy

[![Software License][ico-license]](license.md)
![Stability][ico-stability]

[![nimble](https://raw.githubusercontent.com/yglukhov/nimble-tag/master/nimble_js.png)](https://github.com/yglukhov/nimble-tag)

Haskell-style typeclasses for Nim.

Allows to instantiate collections of functions for a given type or type constructor.

## Install

```bash
$ nimble install classy
```

## Usage

```nim
import classy, future

typeclass Functor, F[_]:
  # proc map[A, B](fa: F[A], g: A -> B): F[B]
  proc `$>`[A, B](fa: F[A], b: B): F[B] =
    fa.map((a: A) => g)

instance Functor, seq[_]
assert: (@[1, 2, 3] $> "a") == @["a", "a", "a"]
```
## Documentation

Module documentation is located [here](https://nigredo-tori.github.io/classy/head/classy.html).

Also refer to [example](example.nim) for a quick tutorial.

## Testing

```bash
$ nim tests
```

## Stability

Highly experimental. API and behaviour subject to change.

## Credits

- [nigredo-tori][link-author]

## License

The Unlicense. Please see [License File](license.md) for more information.

[ico-license]: https://img.shields.io/badge/license-Unlicense-brightgreen.svg?style=flat-square
[ico-stability]: https://img.shields.io/badge/stability-experimental-orange.svg?style=flat-square

[link-author]: https://github.com/nigredo-tori
