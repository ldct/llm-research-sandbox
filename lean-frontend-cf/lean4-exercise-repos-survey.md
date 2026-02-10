# Lean 4 Textbook / Course Repositories with Exercise Files

Survey date: 2025-02-10

---

## 1. Mathematics in Lean (MIL) ✅ ALREADY DONE
- **Repo**: https://github.com/leanprover-community/mathematics_in_lean
- **Mathlib dep**: Yes
- **Exercise/Solution pattern**: `MIL/C*/S*.lean` exercises with `sorry`, paired `solutions/` directory
- **Status**: Already integrated

---

## 2. Formalising Mathematics 2026 (Buzzard/Mehta, Imperial) ⭐ TOP PRIORITY
- **Repo**: https://github.com/b-mehta/formalising-mathematics-notes
- **Older version**: https://github.com/ImperialCollegeLondon/formalising-mathematics-2024
- **Stars**: 88 (2026 edition)
- **Lean toolchain**: `leanprover/lean4:v4.26.0`
- **Mathlib dep**: YES (`mathlib v4.26.0`)
- **Exercise files**: 82 exercise `.lean` files across 21 sections, **327 sorries total**
- **Solution files**: 65 solution `.lean` files in `Solutions/` subdirectory
- **Solutions coverage**: Sections 01–16 fully covered (65/66 sheets). Sections 17–21 (commutative algebra, curves/surfaces, graph theory, algebraic number theory, combinatorics) have NO solutions yet.
- **Exercise format**: Sheets with `sorry` placeholders, numbered Sheet1.lean through Sheet8.lean per section
- **Topics**: Logic, reals, functions, sets, groups, orderings/lattices, subgroups/homomorphisms, finiteness, bijections/isomorphisms, types, topological spaces, filters, vector spaces, measure theory, UFDs/PIDs, number theory, commutative algebra, curves/surfaces, graph theory, algebraic number theory, combinatorics
- **Quality**: Excellent — comprehensive coverage from beginner to advanced, most recent Lean/Mathlib version
- **Notes**: This is the active 2026 course repo maintained by Bhavik Mehta. Supersedes the 2024 Imperial repo. Solutions for later sections still being added.

---

## 3. Mechanics of Proof / math2001 (Heather Macbeth) ⭐ HIGH PRIORITY
- **Repo**: https://github.com/hrmacbeth/math2001
- **Stars**: 330
- **Lean toolchain**: `leanprover/lean4:v4.3.0`
- **Mathlib dep**: YES (also uses Duper and autograder)
- **Exercise files**: 10 chapters of lecture notes with inline exercises (sorry), plus 11 homework files (hw0-hw10)
- **Homework sorry count**: hw0(1), hw1(5), hw2(5), hw3(6), hw4(8), hw5(7), hw6(6), hw7(6), hw8(6), hw9(12), hw10(23) = **~90 homework exercises**
- **Total sorries**: 573 across all files
- **Solution files**: Exercises are embedded in lecture chapters; homeworks have NO provided solutions (they're student assignments)
- **Topics**: Proofs by calculation, proofs with structure, parity/divisibility, logic, induction, number theory, functions, sets, relations
- **Custom library**: Has its own `Library/` with custom tactics (addarith, cancel, exhaust, numbers, rel, etc.)
- **Notes**: The lecture files themselves contain many solved examples alongside the sorry exercises. Homework files are pure exercises (no solutions provided).

---

## 4. How to Prove It with Lean (Dan Velleman) ✅ DONE
- **Repo**: https://github.com/djvelleman/HTPILeanPackage
- **Lean toolchain**: `leanprover/lean4:v4.26.0` (very recent!)
- **Mathlib dep**: YES (`mathlib v4.26.0`)
- **Exercise files**: 6 exercise files: Chap3Ex(23), Chap4Ex(37), Chap5Ex(46), Chap6Ex(46), Chap7Ex(47), Chap8Ex(59) = **258 exercises total**
- **Solution files**: NO solution files included (exercises only, uses `done` instead of `sorry` as placeholder)
- **Custom library**: `HTPILib/` with chapter-specific support (Chap3-8) + HTPIDefs
- **Exercise format**: Named theorems like `Exercise_3_2_1a`, very clean structure
- **Topics**: Propositional logic, quantifiers, set theory, relations, functions, mathematical induction, infinite sets
- **Output file**: `htpi-all.lean` (8287 lines: 6799 library + 1441 exercises, compiles in ~37s on REPL)

---

## 5. Hitchhiker's Guide to Logical Verification (2025 edition) ⭐ HIGH PRIORITY
- **Repo**: https://github.com/lean-forward/logical_verification_2025
- **Other editions**: [2024](https://github.com/lean-forward/logical_verification_2024), [2023](https://github.com/blanchette/logical_verification_2023)
- **Stars**: 89 (2025), 115 (2023)
- **Lean toolchain**: `leanprover/lean4:v4.14.0`
- **Mathlib dep**: YES (`mathlib @ "stable"`)
- **Exercise files**: 14 ExerciseSheets + 12 HomeworkSheets = **26 exercise files**
- **Exercise sorry count**: 143 (exercise sheets) + 92 (homework sheets) = **~235 exercises**
- **Solution files**: NO solutions included in repo (solutions likely distributed separately to students)
- **Structure**: Clean `LoVe01..LoVe14` naming, with `_Demo.lean`, `_ExerciseSheet.lean`, `_HomeworkSheet.lean` per topic
- **Topics**: Types & terms, programs & theorems, backward proofs, forward proofs, functional programming, inductive predicates, effectful programming, metaprogramming, operational semantics, Hoare logic, denotational semantics, logical foundations, basic mathematical structures, rational & real numbers
- **Notes**: CS/PL-focused (not pure math). Demos contain the worked examples that correspond to exercises.

---

## 6. Theorem Proving in Lean 4 (TPIL4) — MODERATE PRIORITY
- **Repo**: https://github.com/leanprover/theorem_proving_in_lean4
- **Stars**: 233
- **Lean toolchain**: `leanprover/lean4:v4.27.0-rc1` (book project via Verso)
- **Mathlib dep**: NO (pure Lean 4, no Mathlib)
- **Exercise files**: Exercises embedded in chapter .lean files with `sorry`
- **Total sorries**: ~105 exercises across 7 chapters
- **Key chapters**: PropositionsAndProofs(31), QuantifiersEquality(26), InductionAndRecursion(19), InteractingWithLean(9), InductiveTypes(6), Examples(8), Tactics(6)
- **Solution files**: NO separate solutions
- **Notes**: These are the canonical Lean 4 reference exercises. No Mathlib dependency means they test pure Lean 4 reasoning. Book is built with Verso framework.

---

## 7. Functional Programming in Lean — LOW PRIORITY
- **Repo**: https://github.com/leanprover/fp-lean
- **Stars**: 141
- **Lean toolchain**: Latest (Verso book project)
- **Mathlib dep**: NO
- **Exercise files**: Very few inline `sorry` (~8 files with sorry, mostly in ProgramsProofs)
- **Notes**: Primarily a programming book, not a theorem proving exercise book. Exercises are described in prose ("write a function that...") rather than as sorry-bearing theorem statements. Limited value for REPL testing.

---

## 8. Natural Number Game (NNG4) — SPECIAL CASE
- **Repo**: https://github.com/leanprover-community/NNG4
- **Stars**: 288
- **Lean toolchain**: `leanprover/lean4:v4.23.0`
- **Mathlib dep**: YES
- **Exercise files**: 182 .lean files with game levels across worlds (Addition, AdvAddition, Multiplication, AdvMultiplication, Algorithm, Implication, LessOrEqual)
- **Notes**: Uses the GameServer framework — levels are defined with custom DSL (`Statement`, `Conclusion`), NOT standard `theorem ... sorry` format. Would need custom extraction to work as REPL exercises. The proofs are provided inline (it's a web game with hints). Not directly usable without adaptation.

---

## 9. Simons 2025 Workshop (Macbeth) — BONUS
- **Repo**: https://github.com/hrmacbeth/Simons2025
- **Lean toolchain**: `leanprover/lean4:v4.21.0-rc3`
- **Mathlib dep**: YES
- **Exercise files**: Lectures with sorry in Geometry, NumberTheory, RealAnalysis, StructuresAndClasses, Metaprogramming
- **Solution files**: YES — `Solutions/` directory with Geometry, NumberTheory, StructuresAndClasses solutions
- **Notes**: Smaller dataset but has solutions paired with exercises. Recent workshop material.

---

## 10. GlaMS Formal 2024 — BONUS  
- **Repo**: https://github.com/glams-lean-2024/formal-2024
- **Mathlib dep**: YES
- **Exercise files**: Workshops (1-7), Homeworks (1-6), Exercises, plus MIL references
- **Solution files**: YES — full solutions for workshops, homeworks, exercises, and tutorials

---

## Summary: Best Repos for REPL Exercise Testing

| Repo | Exercises | Solutions | Mathlib | Lean Version | Priority |
|------|-----------|-----------|---------|--------------|----------|
| MIL (already done) | ~200+ | ✅ Yes | ✅ | v4.x | ✅ Done |
| **Buzzard/Mehta Formalising Math 2026** | **327 sorry (82 files)** | **✅ Yes (65 files, Sec01-16)** | **✅** | **v4.26.0** | **⭐ TOP** |
| **Macbeth math2001** | **~573 sorry** | **Partial (lectures have examples)** | **✅** | **v4.3.0** | **⭐ HIGH** |
| **HTPI Velleman** | **258** | **❌ No** | **✅** | **v4.26.0** | **⭐ HIGH** |
| **Hitchhiker's Guide 2025** | **~235** | **❌ No** | **✅** | **v4.14.0** | **⭐ HIGH** |
| TPIL4 | ~105 | ❌ No | ❌ | v4.27.0-rc1 | Medium |
| Simons2025 | ~50 | ✅ Partial | ✅ | v4.21.0-rc3 | Bonus |
| GlaMS formal-2024 | ~80+ | ✅ Yes | ✅ | v4.x | Bonus |
| FP Lean | ~8 | ❌ No | ❌ | latest | Low |
| NNG4 | ~100+ | Built-in | ✅ | v4.23.0 | Special (needs adaptation) |
