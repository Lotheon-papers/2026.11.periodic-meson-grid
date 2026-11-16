# Tests de proximité à une grille périodique

**Document de travail méthodologique — version du 16 novembre 2026.**
Étude de l'étalonnage conditionnel, appliquée à cinq masses de mésons. Le
document est proposé pour discussion et révision, sans revendication
d'évaluation par les pairs.

Son apport est le calcul exact de l'effet de la phase des extrema sur la
référence ajustée M1, accompagné des minima des trois références sur les
bandes retenues et d'un dossier de reproductibilité. Les principes du
conditionnement, de la loi d'Irwin–Hall et de la randomisation sont classiques.
La section 1.1 de chaque article présente les travaux antérieurs, la comparaison
avec ces résultats et la portée de la recherche bibliographique ciblée.

Le corpus est un cas d'étude intentionnel et rétrospectif : trois masses
précises et deux résonances aux bandes plus larges permettent de distinguer
les variations du score et de l'extremum supérieur. Les états exclus et les
limites de cette sélection sont explicités dans les deux manuscrits.
Axiophysis est un laboratoire interactif de recherche et de simulation en
physique, qui permet d'explorer des modèles à partir de lois, de métriques et
de conditions initiales explicites. Son module Phylab structure une démarche
de recherche itérative autour des hypothèses, des expériences numériques,
des résultats et des rapports. Phylab a été utilisé pour explorer ce cas
d'étude ; les calculs et les preuves livrés sont reproduits avec Python et Lean.

| Élément | Fichier |
|---|---|
| Manuscrit français | [fr/article.tex](fr/article.tex) |
| PDF français | [fr/article.pdf](fr/article.pdf) |
| Manuscrit anglais | [en/article.tex](en/article.tex) |
| English PDF | [en/article.pdf](en/article.pdf) |
| Preuve Lean autonome | [lean/Preuve.lean](lean/Preuve.lean) |
| Mode d'emploi Lean et portée de la formalisation | [lean/README.md](lean/README.md) |
| Masses et calcul rationnel | [reproductibilite/Masses.csv](reproductibilite/Masses.csv) · [reproductibilite/Calculs.py](reproductibilite/Calculs.py) |
| Contrôles d'audit et sortie conservée | [reproductibilite/Verifier.py](reproductibilite/Verifier.py) · [reproductibilite/verification.txt](reproductibilite/verification.txt) |

## Compiler les deux manuscrits

Avec TeX Live ou une distribution LaTeX équivalente, lance deux compilations dans chaque sous-dossier pour résoudre les références.

```bash
(cd fr && pdflatex -halt-on-error article.tex && pdflatex -halt-on-error article.tex)
(cd en && pdflatex -halt-on-error article.tex && pdflatex -halt-on-error article.tex)
python3 reproductibilite/Calculs.py
python3 reproductibilite/Verifier.py
```

Une alternative sans installation complète de TeX Live est Tectonic (version
utilisée pour les PDF livrés : 0.17.0). Il télécharge les ressources TeX lors
du premier lancement et résout automatiquement les références :

```bash
tectonic fr/article.tex
tectonic en/article.tex
```

Les PDF livrés sont au format A4. Les contrôles supplémentaires
utilisent uniquement la bibliothèque standard Python, une graine fixée et
200 000 tirages par configuration. Ils comparent les sorties exactes, comptent
directement les antécédents de la densité, explorent 334 configurations et
recoupent les probabilités par Monte-Carlo. Ces contrôles échantillonnés ne
remplacent pas les preuves de minima globaux. Le rejeu Lean est décrit dans
[lean/README.md](lean/README.md).

Les deux textes partagent les mêmes valeurs et énoncés. L'auteur est Frederic
Loth, chercheur indépendant. Les sources, PDF, données et preuves forment le
dossier de ce document de travail.

The French and English sources contain the same scientific results. The Lean file and the rational Python program are shared by both versions.

## Dépôt et archivage

Ce dossier constitue la racine du dépôt autonome
`Lotheon-papers/2026.11.periodic-meson-grid`. Le nom associe l'année et le mois
à la traduction anglaise du sujet : « periodic meson grid ».

Les versions diffusées sont identifiées par des releases GitHub. Après
activation de l'intégration Zenodo pour ce dépôt, chaque nouvelle release
publiée est archivée et reçoit un DOI. L'archive regroupe les deux langues,
les données, les calculs et les preuves de cette publication.
[Documentation GitHub–Zenodo](https://docs.github.com/en/repositories/archiving-a-github-repository/referencing-and-citing-content).
