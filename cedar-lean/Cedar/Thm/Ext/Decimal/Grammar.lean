/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

public import Cedar.Spec.Ext.Decimal
public import Std.Data.String
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-! # Decimal grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates and the
value function — as a direct, parser-independent transcription of the decimal grammar. Each
production becomes a predicate, and `IsDecimalValue s v` says the string `s` is their rendering
*and* `v` is the value the grammar assigns to it. Both halves of the grammar therefore share a
single decomposition, and `IsWfDecimal` is just its projection. The lemmas connecting these
definitions to `Decimal.parse` (in particular the digit-string ↔ `toInt?'`/`toNat?'` bridges) live
in `Cedar.Thm.Ext.Decimal.Lemmas`.

`Sign ::= ['-']` uses the shared `IsWfSign` predicate. The decimal-specific `Natural` and
`Fraction` productions are named locally using the shared digit predicates `IsDigits` and
`IsDigitsUpTo`; their string-to-number bridges live in `Cedar.Thm.Data.String`. -/

/-- The grammar's `Natural ::= Digit⁺`: the unsigned natural-number production. An `abbrev` for
    the shared `IsDigits` predicate, so every `IsDigits` lemma applies without unfolding. -/
-- ANCHOR: IsNatural
public abbrev IsNatural (s : String) : Prop := IsDigits s
-- ANCHOR_END: IsNatural

/-- The grammar's `Fraction ::= Digit{1,4}`: 1 to `DECIMAL_DIGITS` digits, an instance of the
    shared bounded-digits predicate. -/
-- ANCHOR: IsWfFrac
public def IsWfFrac (s : String) : Prop :=
  IsDigitsUpTo DECIMAL_DIGITS s
-- ANCHOR_END: IsWfFrac

/-- The grammar's `sign = -1 if Sign is '-', else 1`. -/
-- ANCHOR: signValue
public def signValue (sign : String) : Int := if sign = "-" then -1 else 1
-- ANCHOR_END: signValue

/-- The grammar's value function, applied to an already-decomposed literal:

      value = sign × (nat(Natural) × 10⁴ + nat(Fraction) × 10^(4 − |Fraction|))

    `IsWfFrac fraction` bounds `fraction.length ≤ DECIMAL_DIGITS`, so the `Nat` subtraction in the
    second exponent never clamps on a well-formed field. -/
-- ANCHOR: decimalValue
public def decimalValue (sign natural fraction : String) : Int :=
  signValue sign *
    (fieldValue natural * Int.pow 10 DECIMAL_DIGITS
     + fieldValue fraction * Int.pow 10 (DECIMAL_DIGITS - fraction.length))
-- ANCHOR_END: decimalValue

/-- `v` is the value of the decimal literal `s`: `s` is the rendering of a well-formed
    `Sign ::= ['-']`, `Natural ::= Digit⁺`, `'.'`, and `Fraction ::= Digit{1,4}`, concatenated in
    that order, and `v` is what the grammar's value function assigns to those fields.

    Phrasing the spec relationally over the rendering bakes in the separator and field order
    without introducing a record for this single flat production, and lets syntax and value share
    one decomposition: the existential supplies the split, so no string surgery
    (`front`/`drop`/`splitToList`) and no `Option` appear here. This is a direct transcription of
    the grammar's character-level productions, independent of any string-to-number parser.

    The relation is single-valued (`isDecimalValue_unique`), so it does pin down a function. -/
-- ANCHOR: IsDecimalValue
public def IsDecimalValue (s : String) (v : Int) : Prop :=
  ∃ sign natural fraction,
    s = sign ++ natural ++ "." ++ fraction ∧
    IsWfSign sign ∧
    IsNatural natural ∧
    IsWfFrac fraction ∧
    v = decimalValue sign natural fraction
-- ANCHOR_END: IsDecimalValue

/-- Well-formed decimal syntax: `s` has a value. Since the value function is total on the
    grammar's fields, this says exactly that `s` parses as `Sign Natural '.' Fraction`. -/
-- ANCHOR: IsWfDecimal
public def IsWfDecimal (s : String) : Prop := ∃ v, IsDecimalValue s v
-- ANCHOR_END: IsWfDecimal

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
