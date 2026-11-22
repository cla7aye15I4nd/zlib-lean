import unittest

from tools.check_baseline_equiv import (
    BASELINE_PROVED_GOALS,
    BASELINE_REQUIRED_GOALS,
    extract_goal_defs,
    extract_named_decl,
    normalize_tokens,
    strip_lean_comments,
)


class BaselineEquivUnitTest(unittest.TestCase):
    def test_baseline_goal_counts(self) -> None:
        self.assertEqual(len(BASELINE_PROVED_GOALS), 124)
        self.assertEqual(len(set(BASELINE_PROVED_GOALS)), 124)
        self.assertEqual(len(BASELINE_REQUIRED_GOALS), 99)
        self.assertEqual(len(set(BASELINE_REQUIRED_GOALS)), 99)

    def test_strip_lean_comments_preserves_code_and_strings(self) -> None:
        src = '''/-!
Module comment with nested /- comment -/ inside
-/
namespace Foo
/-- Old docstring mentioning `docs/en/deviations.md` -/
def Goal.sample : Prop := -- trailing comment
  ∀ s : String, s = "-- not a comment /- still string -/"
end Foo
'''
        stripped = strip_lean_comments(src)
        self.assertNotIn("Module comment", stripped)
        self.assertNotIn("Old docstring", stripped)
        self.assertNotIn("trailing comment", stripped)
        self.assertIn('"-- not a comment /- still string -/"', stripped)
        self.assertIn("def Goal.sample : Prop :=", stripped)

    def test_docstring_edit_keeps_goal_defs_equal(self) -> None:
        old = '''namespace ZlibF.Spec.Public
/-- Old ref docs/en/foo.md -/
def Goal.foo_safety : Prop := ∀ n : Nat, n = n
end ZlibF.Spec.Public
'''
        new = '''namespace ZlibF.Spec.Public
/-- Clean updated docstring pointing to docs/SAFETY.md -/
def Goal.foo_safety : Prop :=
  -- harmless inline comment
  ∀ n : Nat, n = n
end ZlibF.Spec.Public
'''
        old_s = strip_lean_comments(old)
        new_s = strip_lean_comments(new)
        self.assertEqual(normalize_tokens(old_s), normalize_tokens(new_s))
        self.assertEqual(extract_goal_defs(old_s), extract_goal_defs(new_s))

    def test_code_mutation_detected(self) -> None:
        old = '''def Goal.foo_safety : Prop := ∀ n : Nat, n < 10 → n = n
'''
        mutated = '''def Goal.foo_safety : Prop := ∀ n : Nat, n ≤ 10 → n = n
'''
        old_goals = extract_goal_defs(strip_lean_comments(old))
        mut_goals = extract_goal_defs(strip_lean_comments(mutated))
        self.assertNotEqual(old_goals, mut_goals)
        self.assertEqual(list(old_goals.keys()), ["Goal.foo_safety"])

    def test_extract_named_decl(self) -> None:
        code = strip_lean_comments(
            """inductive PublicEntry : Prop → Type where
  | a : PublicEntry True
def Goal.whole_library_safety : Prop := True
"""
        )
        decl = extract_named_decl(code, "inductive PublicEntry")
        self.assertIn("PublicEntry : Prop → Type", decl)
        self.assertNotIn("Goal.whole_library_safety", decl)


if __name__ == "__main__":
    unittest.main()
