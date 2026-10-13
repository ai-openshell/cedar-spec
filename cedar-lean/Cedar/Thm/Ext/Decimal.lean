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

public import Cedar.Thm.Ext.Decimal.Lemmas

import all Cedar.Data.Int64
import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Ext.Decimal.Grammar
import all Cedar.Thm.Ext.Decimal.Lemmas

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-- Completeness of `Decimal.parse`: if the grammar assigns `s` the value `d.toInt`, then parsing
    accepts the string as `d`. Well-formedness is not a separate hypothesis — `IsDecimalValue`
    already asserts that `s` is a rendering of the grammar's productions. -/
public theorem parse_complete (s : String) (d : Decimal)
    (hval : IsDecimalValue s d.toInt) : Decimal.parse s = some d := by
  rw [parse_eq_decimal?_of_isDecimalValue hval]
  exact Int64.ofInt?_toInt d

/-- Soundness of `Decimal.parse`: if parsing succeeds, then the input is a well-formed rendering
    whose grammar value is exactly the returned decimal's value. (The value is automatically in
    `Int64` range, since `d : Decimal = Int64`, so no range conjunct is stated.) -/
public theorem parse_sound (s : String) (d : Decimal) (h : Decimal.parse s = some d) :
    IsDecimalValue s d.toInt := by
  unfold Decimal.parse at h
  split at h
  · exact absurd h (by simp)
  · rename_i left right h_ne h_split
    split at h
    · rename_i l r heq_l heq_r
      have h_len : 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS := by
        by_contra hc; simp [hc] at h
      simp only [show 0 < right.length ∧ right.length ≤ DECIMAL_DIGITS from h_len,
        Decimal.decimal?] at h
      -- the left field's `toInt?'` witness splits into the grammar's `Sign` and `Natural`
      obtain ⟨sign, natural, rfl, hs, hn⟩ :=
        sign_nat_of_toInt?'_isSome (s := left) (by rw [heq_l]; rfl)
      have hf : IsWfFrac right := ⟨isDigits_of_toNat?'_isSome (by rw [heq_r]; rfl), h_len.2⟩
      refine ⟨sign, natural, right, ?_, hs, hn, hf, ?_⟩
      · have hjoin := join_splitToList h_split
        simp only [String.append_assoc] at hjoin ⊢
        exact hjoin
      · rw [← parser_value_eq_decimalValue hs hn heq_l heq_r]
        exact Int64.ofInt?_some_toInt h
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- Parsing the canonical string representation of a decimal returns the same decimal. -/
public theorem parse_toString_roundtrip (d : Decimal) :
    Decimal.parse (toString d) = some d :=
  parse_complete (toString d) d (isDecimalValue_toString d)

/-- Failure characterization for `Decimal.parse`: parsing rejects exactly the strings the grammar
    assigns no value at all, and those whose value overflows the `Int64` range. Since the second
    disjunct exhibits a value, it entails well-formedness — the two cases are mutually
    exclusive. -/
public theorem parse_eq_none_iff (s : String) :
    Decimal.parse s = none ↔ (∀ v, ¬ IsDecimalValue s v) ∨
    ∃ v, IsDecimalValue s v ∧ (v < Int64.MIN ∨ v > Int64.MAX) := by
  constructor
  · -- → direction: parse s = none implies no value or an out-of-range one
    intro h
    by_cases hwf : IsWfDecimal s
    · -- s has a value, so the failure came from the range check
      obtain ⟨v, hv⟩ := hwf
      rw [parse_eq_decimal?_of_isDecimalValue hv] at h
      exact Or.inr ⟨v, hv, Int64.ofInt?_none_iff.mpr h⟩
    · exact Or.inl (fun v hv => hwf ⟨v, hv⟩)
  · -- ← direction: no value, or an out-of-range one, implies parse s = none
    rintro (h | ⟨v, hv, hovf⟩)
    · by_contra hne
      have ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hne
      exact h d.toInt (parse_sound s d hd)
    · rw [parse_eq_decimal?_of_isDecimalValue hv]
      exact Int64.ofInt?_none_iff.mp hovf

/-- `toString` is injective: distinct decimals produce distinct strings. -/
public theorem toString_injective (d d' : Decimal) (h : toString d = toString d') : d = d' := by
  have h1 := parse_toString_roundtrip d
  have h2 := parse_toString_roundtrip d'
  rw [h] at h1
  rw [h1] at h2
  injection h2

/-- Equal normal form iff equal value: normalization decides decimal equality. -/
public theorem normalize_eq_iff_parse_eq (s s' : String) :
    normalize s = normalize s' ↔ Decimal.parse s = Decimal.parse s' := by
  constructor
  · intro h
    unfold normalize at h
    match hps : Decimal.parse s, hps' : Decimal.parse s' with
    | .some d, .some d' =>
      simp [hps, hps', Option.map] at h
      exact congrArg _ (toString_injective d d' h)
    | .some d, .none => simp [hps, hps', Option.map] at h
    | .none, .some d' => simp [hps, hps', Option.map] at h
    | .none, .none => rfl
  · intro h
    simp [normalize, h]

end Cedar.Thm.Decimal
