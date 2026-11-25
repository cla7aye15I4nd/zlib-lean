import C99.Proof.Mem
import C99.Proof.WP
import C99.Proof.Hoare
import C99.Proof.AutoWP

/-!
# Generic `C99` Safety Proof Infrastructure (`C99.Proof`)

Umbrella module importing memory/representation lemmas (`C99.Proof.Mem`),
terminating weakest-precondition rules (`C99.Proof.WP`), continuation-polymorphic
Hoare combinators (`C99.Proof.Hoare`), and kernel-checked WP automation (`C99.Proof.AutoWP`).
-/
