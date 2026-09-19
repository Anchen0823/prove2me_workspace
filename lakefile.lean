import Lake
open Lake DSL
package «prove2me» where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"
-- The Sondow certificates in Solutions/ lean on this scratch helper, so it has
-- to be a real Lake module rather than a file that merely sits in examples/.
-- It is not a default target; it is only ever built as a dependency.
lean_lib «RosserLcmBlocks» where
  roots := #[`examples.«five-primes».RosserLcmBlocks]
-- Same story for the Spencer (1980) route to the general-n semi-magic rung of
-- mission V: it is a small development split over files that import each
-- other, so the pieces have to be real Lake modules.  Not a default target.
lean_lib «SpencerRoute» where
  roots := #[`examples.«magic-squares».spencer.Spencer,
             `examples.«magic-squares».spencer.HallSupport,
             `examples.«magic-squares».spencer.SupportSplit,
             `examples.«magic-squares».spencer.Recursion,
             `examples.«magic-squares».spencer.Aggregate,
             `examples.«magic-squares».spencer.Rank,
             `examples.«magic-squares».spencer.Sharp]
-- Every library declares an empty `roots` plus explicit globs. Without this,
-- Lake treats the library name as a *module* and looks for a root file
-- (`Definitions.lean` / `Theorems.lean` / `Solutions.lean`); those files do not
-- exist here, so resolving their imports failed and every library target died
-- with "some modules have bad imports" during job computation. Listing the
-- glob explicitly means only files that really exist ever enter the module set.
lean_lib «Definitions» where
  roots := #[]
  globs := #[.submodules `Definitions]
lean_lib «Theorems» where
  roots := #[]
  globs := #[.submodules `Theorems]
@[default_target]
lean_lib «Solutions» where
  roots := #[]
  globs := #[.submodules `Solutions]
