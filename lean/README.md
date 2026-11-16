# Formalisation Lean

[Preuve.lean](Preuve.lean) est un fichier autonome. Le projet fixe Lean à 4.19.0, commit 6caaee842e94, et Mathlib à la révision c44e0c8ee63ca166450922a373c7409c5d26b00b. Le manifeste fixe les dépendances transitives.

## Rejouer sous WSL

Installe Lean via Elan en suivant https://lean-lang.org/install/manual/. Depuis le dossier `lean/`, sous Bash, récupère le cache des modules importés puis compile.

```bash
mapfile -t modules < <(awk '/^import / {print $2}' Preuve.lean)
lake exe cache get "${modules[@]}"
lake build
lake env lean Preuve.lean
```

La dernière commande imprime les dépendances axiomatiques. Le [journal](journal-lean.txt) contient 28 énoncés compilés. Le fichier ne contient aucun `sorry` et le journal ne rapporte aucune dépendance à `sorryAx`.

Le rejeu du 15 novembre 2026 a confirmé la compilation avec les neuf révisions
de dépendances du manifeste. Le fichier comprend 30 théorèmes publics et cinq
théorèmes privés ; le journal imprime les axiomes de 28 théorèmes publics.
Seuls `propext`, `Classical.choice` et `Quot.sound` apparaissent dans ces sorties.
La correspondance ci-dessous précise la portée des résultats formalisés.

## Correspondance avec l'article

| Résultat | Énoncé ou groupe d'énoncés |
|---|---|
| Distance au point de grille le plus proche et variations du score | `AuditV10.nearest`, `AuditV10.distance_shift_bound`, `AuditV10.joint_phase_interval` |
| Mesure de l'ensemble de phases de M3 et minimum exact sur le domaine | `PhaseMeasure.lower_bound`, `PhaseMeasure.exact_witness` |
| Volume de Lebesgue du simplexe, en dimension arbitraire | `SimplexVolume.volume_simplex` |
| Queue dans le cube unité pour un seuil au plus égal à 1 et rapport des tailles | `SimplexVolume.unit_cube_lower_tail`, `SimplexVolume.cube_tail_ratio` |
| Repliement uniforme d'une période normalisée | `OnePeriod.folded_error`, `OnePeriod.folded_volume` |
| Fraction exacte M1 au témoin, quantile et taille conditionnelle à 5 % | `ControleV11.exact_m1_witness`, `ControleV11.m1_threshold_bracket`, `ControleV11.conditional_size_arithmetic` |
| Encadrements numériques pour M2 | `AuditV10.m2_root_bracket_arithmetic`, `AuditV10.m2_value_bracket_arithmetic` |
| Passage des hypothèses de dérivation et de monotonie à un minimum global | `Optimisation.rectangle_minimum`, `Optimisation.unique_bracketed_root`, `Optimisation.minimum_at_root` |

Le fichier regroupe toutes les vérifications Lean livrées pour les deux manuscrits. La formalisation intégrale de l'article reste ouverte. Le passage du modèle iid uniforme aux lois d'ordre conditionnelles, la décomposition des densités et convolutions de M1 et M2, et les hypothèses de dérivation des objectifs sont démontrés analytiquement dans les deux manuscrits. Les lemmes d'optimisation déclarent explicitement les hypothèses qu'ils utilisent.
