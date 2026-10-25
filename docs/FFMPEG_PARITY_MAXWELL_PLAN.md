# Plan Maxwell pour une compatibilité FFmpeg mesurée et vérifiable

## 0. Mandat

Objectif : faire évoluer `lean-ffmpeg` d'un prototype MP4 à une couche multimédia typée, portable et progressivement vérifiable, capable de déléguer fidèlement aujourd'hui et de remplacer sélectivement FFmpeg demain.

Le projet ne promet pas une domination globale « 1:1 meilleure partout ». Chaque capacité doit avoir un contrat versionné, un oracle, des preuves ou tests, des métriques et une décision de backend explicite.

Référence initiale :

- dépôt `lean-ffmpeg` ;
- commit de départ `386c07663a214aba2fbbf563abb561a08ddc8d52` ;
- Lean `leanprover/lean4:v4.31.0` ;
- `lean-sys` épinglé au commit `9a3fda9180d8e9a2e429ca38046b74467f68866b` ;
- FFmpeg de référence à pinner dans le registre généré, avec hash du binaire, configuration et bibliothèques ;
- Maxwell : `https://github.com/Th0rgal/maxwell`.

## 1. Contrats de succès

Une capacité est admise dans le périmètre contractuel seulement si elle est qualifiée par build, plateforme et backend :

- `independent_verified` : implémentation indépendante vérifiée et comparée ;
- `independent_tested` : implémentation indépendante testée mais pas entièrement prouvée ;
- `delegated_faithful` : délégation structurée vers le build FFmpeg de référence ;
- `translated_partial` : traduction partielle avec limites explicites ;
- `approximate` : équivalence sémantique tolérée, non bit-exacte ;
- `unsupported` : refus explicite avant exécution ;
- `untested` : jamais présenté comme supporté.

Les axes sont séparés :

1. compatibilité CLI et diagnostics ;
2. couverture de formats, codecs, filtres et I/O ;
3. fidélité média, timestamps et métadonnées ;
4. performance, mémoire, latence et énergie ;
5. sécurité, robustesse et limites de ressources ;
6. portabilité et reproductibilité ;
7. vérifiabilité et taille de la trusted computing base ;
8. licence et redistribuabilité.

## 2. Boucle Maxwell obligatoire

Chaque chantier suit la boucle :

```text
Conjecture -> Specification -> Certification -> telemetry -> priors -> prochaine vague
```

### Conjecture

Produire plusieurs hypothèses concurrentes et courtes : architecture, réduction de bug, corpus, représentation ou optimisation. Chaque branche reçoit :

- `branch_id` stable ;
- `race_group` ;
- `p` ;
- `impact` ;
- `effort_p50` et `effort_p90` en tokens ;
- hypothèse falsifiable ;
- oracle prévu ;
- condition d'abandon.

Toute branche dont `effort_p50 > 6000` est récursivement découpée avant certification. Chaque micro-tâche vise un fichier, une propriété ou un harness autonome.

### Specification

Formaliser la cible et ses contre-exemples :

- entrée/sortie normalisée ;
- comportement FFmpeg de référence ;
- classe d'équivalence ;
- limites et non-objectifs ;
- mutants négatifs ;
- métriques ;
- hash de spécification.

Passer `turbo-lean --json audit-spec` avec zéro spécification vacue, triviale ou masquée, puis une suite de mutants qui démontre que le test détecte réellement les régressions.

### Certification

Admettre une branche uniquement après :

- `lake build` ou `turbo-lean check` ;
- `turbo-lean pr-verify` lorsque le périmètre le permet ;
- tests différentiels contre FFmpeg épinglé ;
- corpus adversarial et fuzzing pour les frontières natives ;
- vérification des sorties, erreurs, ressources et déterminisme ;
- audit des axiomes, licences et dépendances ;
- quorum de validation si la décision est architecturale ou contractuelle.

### Gouvernance Maxwell

Utiliser Maxwell pour :

- classer les branches par probabilité, impact et effort ;
- lancer au moins une sonde de falsification par vague ;
- annuler les frères d'une course dès qu'une branche est certifiée ou réfutée ;
- couper les branches hors budget ou stagnantes ;
- enregistrer par le contrôleur uniquement les résultats `VALIDATED`, `FALSIFIED`, `PRUNED`, `BLOCKED` ou `FALSE_GOAL` ;
- auditer la télémétrie après chaque vague avec `audit-campaign --fix`.

Les workers ne déclarent pas eux-mêmes leurs coûts ni leurs priors.

### Amorçage et persistance opérationnelle

Épingler d'abord un SHA Maxwell et vérifier le README ainsi que `./scripts/maxwell --help` et l'aide de chaque sous-commande ; ne pas supposer que les options d'une ancienne version de `research-governor` restent valides. Maxwell utilise actuellement Lean 4.35 : l'exécuter dans son propre checkout/toolchain, sans migrer implicitement lean-ffmpeg 4.31 ni modifier le sibling `lean-sys` sale.

Commandes documentées à adapter au checkout Maxwell épinglé :

```sh
./scripts/maxwell rank candidates.json --domain lean_proof --no-remote-priors
./.lake/build/bin/maxwell-core self-test
```

Pour les tâches média non formelles, ne pas inventer un domaine de priors : vérifier les domaines acceptés, conserver une catégorie locale et des priors explicitement estimés si aucun domaine ne convient. Une télémétrie distante indisponible n'autorise pas des métriques inventées ; conserver les événements localement et signaler la dégradation.

Utiliser `watch`, `step`, `record` et `audit-campaign` seulement avec les paramètres confirmés par l'aide de la version épinglée. Une preuve du gouverneur certifie sa règle d'acceptation, pas la correction de FFmpeg, du runner ou des kernels C.

À chaque checkpoint, enregistrer de façon durable : SHA du code et de la spécification, DAG, budgets réels disponibles, branches actives/terminées, preuves, contre-exemples, verdicts de revue et prochaine action. Les continuations reprennent cet état ; elles ne repartent pas d'un récit ni d'un fichier temporaire perdu. Les dépassements de budget, permissions manquantes et indisponibilités externes provoquent un état bloqué explicite, jamais une boucle infinie ni une déclaration de fin.

## 3. Quorums de validation multi-modèles

Les modèles donnent un avis indépendant ; ils ne remplacent jamais l'oracle mécanique.

### Quorum standard

Pour une décision importante : consulter Fable, Astra et Gemini avec le même dossier immuable : diff, spécification, résultats, métriques et questions précises.

La décision est admissible si :

- au moins 2 avis sur 3 convergent ;
- aucun avis ne détecte une contradiction non résolue avec la spécification ;
- l'oracle mécanique et les tests passent ;
- la minorité est conservée comme risque ou expérience à ajouter.

### Quorum renforcé

Obligatoire pour :

- changement de sémantique publique ou de compatibilité historique ;
- choix CLI versus FFI versus implémentation indépendante ;
- ajout d'un protocole réseau, device ou accélérateur matériel ;
- modification de la trusted computing base ;
- décision de licence ou de redistribution ;
- promotion d'un backend indépendant en remplacement par défaut ;
- suppression d'un fallback ;
- déclaration de supériorité de performance ou de sécurité.

Seuil : 3 avis convergents, ou 2 avis convergents accompagnés d'une expérience supplémentaire qui tranche explicitement le désaccord. Toute divergence persistante bloque la promotion et crée une branche Maxwell dédiée.

### Format d'avis

Chaque consultation doit répondre séparément à :

1. la spécification est-elle non vacue et falsifiable ?
2. les preuves/tests mesurent-ils le bon contrat ?
3. quels risques sont absents ?
4. quelle architecture est recommandée et pourquoi ?
5. quelle expérience minimale peut réfuter cette recommandation ?
6. la promotion est-elle `approve`, `approve_with_limits` ou `reject` ?

## 4. Phases et gates

### Phase 0 — Gel du périmètre et baseline

Livrables : registre des capacités, build FFmpeg immuable, environnement, licences, matrice des plateformes, classes d'équivalence et politique des quirks historiques.

Gate : aucune capacité annoncée sans test réel ; baseline reproductible sur Linux x86-64 et macOS ARM64, puis Linux ARM64 et Windows x86-64 avant promotion cross-platform.

### Phase 1 — Harness différentiel

Construire le runner qui capture argv, hashes, environnement, stdout/stderr, code de sortie, artefacts, `ffprobe`, packets, frames, samples, timestamps, métadonnées, ressources, logs et traces.

Comparer succès/échec, erreurs, flux, frames, samples, durée, timestamps, side data, qualité, taille, temps, mémoire et déterminisme.

Gate : aucune comparaison fondée uniquement sur « le fichier s'ouvre » ; les 9 écarts déjà observés deviennent des tests de régression minimisés.

### Phase 2 — Invariants de base

Corriger : timebases, PTS/DTS, edit lists, `-r`, `-ss`, `-t`, durées minuscules, timestamps négatifs, couleur/range/matrice, profondeur/chroma, chaînes de filtres, audio, quiet, JSON et erreurs de chemin.

Gate : zéro divergence critique sur le corpus de régression, avec contre-exemple conservé pour chaque correction.

### Phase 3 — IR streams/graphes/timeline

Remplacer `CliConfig` plate par une représentation typée des inputs, outputs, streams, programmes, maps, graphes, timeline, metadata, ressources, erreurs et politique de backend.

Gate : plan sérialisable et inspectable, validation avant exécution, round-trip CLI/IR, conservation des cas MP4 existants.

### Phase 4 — Compatibilité générale déléguée

Ajouter par vagues : conteneurs, codecs, filtres, `-map`, multi-I/O, sous-titres, metadata, chapitres, bitstream filters, protocoles, devices et diagnostics.

Chaque intégration est marquée `delegated_faithful`, `translated_partial` ou `approximate`.

Gate : couverture mesurée par domaine, entrée malformée testée, chemins sécurisés, plateforme qualifiée, aucune capacité silencieusement ignorée.

### Phase 5 — FFI ciblé

Commencer par probing, packets/frames, remuxing, graphes, buffers mémoire et cancellation. Utiliser une façade C réduite, ABI-pinnée, avec ownership explicite.

Gate : sanitizers, fuzzing, tests de propriété mémoire, cancellation, multi-thread, ABI et absence de régression contre le backend CLI.

### Phase 6 — Kernels indépendants

Cibler uniquement les composants bornés : conversions, rescaling temporel, validation, parsers, remuxers et filtres à oracle mathématique clair.

Gate : spécification indépendante, preuve ou test de propriété, oracle différentiel, corpus adversarial, benchmark réel, fallback explicite.

### Phase 7 — Promotion progressive

Un backend indépendant devient par défaut uniquement si sa couverture, fidélité, erreurs, sécurité, performance, portabilité et rollback sont documentés et validés.

Gate renforcé : quorum Fable/Astra/Gemini selon les règles ci-dessus et comparaison publiée par capability.

## 5. Vagues de travail

Chaque vague Maxwell contient :

1. une sonde `PROBE` de falsification ;
2. au moins deux branches concurrentes `PROVE`, `IMPLEMENT` ou `MEASURE` ;
3. un oracle mécanique ;
4. une spécification mutante ;
5. une décision d'acceptation ;
6. une entrée de télémétrie boss-verified ;
7. une revue de quorum si le changement franchit un gate renforcé ;
8. un audit et une mise à jour des priors.

Ordre initial recommandé :

- Vague A : registre généré et build FFmpeg épinglé ;
- Vague B : harness différentiel reproductible ;
- Vague C : corrections timeline/couleur/durée/diagnostics ;
- Vague D : IR streams/maps/graphes ;
- Vague E : multi-I/O, metadata, sous-titres et bitstream filters ;
- Vague F : protocoles/devices/hwaccel avec périmètres séparés ;
- Vague G : façade FFI ciblée ;
- Vague H : premiers kernels indépendants et promotions mesurées.

Les vagues peuvent être parallélisées seulement lorsque leurs contrats, fichiers et fixtures sont indépendants.

## 6. Corpus obligatoire

Le corpus doit inclure :

- SD à 8K, CFR/VFR, B-frames, timestamps négatifs, durées extrêmes ;
- mono à multicanal, fréquences atypiques, priming et silence ;
- 8/10/12/16 bits, 4:2:0/4:2:2/4:4:4, SDR/HDR10/HLG ;
- rotation, SAR/DAR, chapitres, attachments, cover art et side data ;
- plusieurs programmes, fichiers fragmentés et non seekable ;
- entrées concaténées, corruption et fichiers quasi-valides ;
- fichiers de téléphones, caméras, capture écran, streaming et logiciels concurrents ;
- générateurs de timestamps, mappings, graphes, métadonnées et paramètres valides ;
- mutations de headers, packets et options.

Aucun cas réduit ne doit être supprimé : il devient un test distinct avec provenance et hash.

## 7. Métriques et critères de promotion

Compatibilité : taux de succès, échec concordant, divergence de diagnostics, options/flux/formats/profils couverts.

Fidélité : frames/samples, erreur maximale et moyenne, PSNR/SSIM/VMAF, timestamps, durée, metadata, side data, dispositions et mapping.

Performance : temps total, CPU, débit, mémoire, latence, probing, pipes, FFI et scaling threads.

Robustesse : crash, timeout, corruption, interruption, limites et récupération.

Sécurité : fuzzing, sanitizers, ressources, filesystem, réseau, isolation, CVE, reproductibilité et provenance.

Un rapport de promotion doit séparer :

- bit-exact ;
- équivalence décodée ;
- équivalence perceptuelle ;
- compatibilité CLI ;
- compatibilité diagnostique ;
- comportement historique volontairement reproduit ;
- comportement refusé.

## 8. Sécurité, licences et plateformes

Exécution sans shell interpolation, argv structuré, environnement nettoyé, répertoire isolé, limites CPU/mémoire/fichiers/durée, allowlist de protocoles, contrôle des redirections, validation des chemins, limites de streams et de profondeur de graphe.

Avant toute distribution : licence FFmpeg, configuration GPL/LGPL, bibliothèques optionnelles, codecs externes, matériel, notices, sources et compatibilité avec la licence du projet.

Toute capacité est qualifiée par plateforme et build. Matrice minimale : Linux x86-64, macOS ARM64, Linux ARM64 et Windows x86-64.

## 9. Règles d'arrêt et d'escalade

- Deux échecs du même prompt : ne pas relancer identiquement ; décomposer ou brûler la branche.
- Branche fausse : `FALSE_GOAL`, score nul, contre-exemple conservé.
- Branche stagnante ou hors budget : arrêt Maxwell et télémétrie.
- Désaccord de quorum : bloquer la promotion, créer une expérience discriminante.
- Divergence entre oracle et avis humain : l'oracle gagne pour l'acceptation ; l'avis devient risque ou nouvelle conjecture.
- Impossible de garantir un axe : le contrat est réduit, jamais masqué.

## 10. État persistant attendu

Maintenir dans le dépôt :

- ce plan ;
- le registre généré et sa provenance ;
- les spécifications et mutants ;
- les fixtures minimisées ;
- les rapports différentiels ;
- les décisions de quorum ;
- les rapports de promotion ;
- les leçons de campagne ;
- les hashes des outils, builds et corpus.

Chaque livrable doit être reproductible depuis un checkout propre avec les dépendances épinglées.

## 11. Premier objectif exécutable

La prochaine campagne doit créer, dans cet ordre :

1. `docs/capability-registry.json` généré depuis le build FFmpeg de référence ;
2. `tests/differential/` avec runner, normaliseur, comparateurs et fixtures des écarts connus ;
3. `docs/contracts/` pour les classes d'équivalence et diagnostics ;
4. une première vague Maxwell avec candidats, priors, race groups et oracle ;
5. un rapport de quorum Fable/Astra/Gemini sur le contrat et l'architecture ;
6. la correction certifiée d'un invariant prioritaire, sans modifier silencieusement le périmètre.

La campagne continue jusqu'à ce que tous les gates du périmètre déclaré soient certifiés. Une réduction de périmètre nécessite l'accord explicite de Thomas ; le quorum ne peut pas autoriser seul cet abandon. Les jalons intermédiaires restent partiels et ne constituent pas la fin de l'ambition générale. Il n'existe pas de réussite basée sur une simple compilation ou sur un fichier lisible.

Avant de déclarer la campagne terminée, produire un dossier de clôture : registre complet pour le build contractuel, capacités manquantes et exclusions approuvées, résultats différentiels reproductibles, matrice des plateformes effectivement testées, frontières de preuve/FFI, métriques avec incertitudes, décisions de quorum et procédure de rollback. Les gains sont revendiqués uniquement sur les axes mesurés ; délégation et modèles formels locaux ne comptent pas comme codecs indépendants prouvés.

Contraintes connues à reprendre dans les premiers checkpoints : les tests média antérieurs dépendaient en partie d'un shim diagnostique, pas du runtime normal ; reproduire les défauts avec la résolution runtime corrigée. `turbo-lean ci-verify` rejette actuellement les FFI externes et les affichages `#eval`, et `pr-verify` échoue sur la dépendance sibling `LeanSys` en staging. Créer des tâches pour résoudre ces obstacles ou séparer explicitement les périmètres natif/formel ; ne jamais assimiler un build trusted à une certification untrusted ni supprimer les frontières FFI de l'audit.

## 12. /goal recommandé

```text
Continue l'exécution de docs/FFMPEG_PARITY_MAXWELL_PLAN.md jusqu'à la fin : inspecte l'état réel, exécute les vagues Maxwell dans l'ordre, décompose récursivement les tâches, consulte Fable/Astra/Gemini pour chaque gate renforcé, vérifie chaque résultat avec les oracles et les tests, persiste les artefacts et la télémétrie, corrige les échecs puis reprends. Ne déclare pas la réussite sur compilation seule ; arrête uniquement quand tous les gates du périmètre certifié passent, ou demande une clarification si une décision bloquante ne peut pas être tranchée par le plan et les preuves.
```
