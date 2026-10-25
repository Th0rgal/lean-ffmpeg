# Dossier de Clôture de Campagne — Parité FFmpeg & Qualification Maxwell (`lean-ffmpeg`)

Ce dossier rassemble l'ensemble des livrables, contrats, preuves formelles, tests différentiels et politiques de qualification/rollback exigés par le plan directeur [`docs/FFMPEG_PARITY_MAXWELL_PLAN.md`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/FFMPEG_PARITY_MAXWELL_PLAN.md) (§10 et §11).

---

## 1. Taxonomie de Qualification & Niveaux de Support (§1)

Chaque capacité du registre et du planificateur [`LeanAV.PlanIR.BackendTier`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L31-L49) est classée dans exactement l'un des sept niveaux suivants :
1. **`independent_verified`** : Implémenté en Lean/C-SIMD hors de FFmpeg, prouvé formellement (`0 sorryAx`, `0` alerte `turbo-lean --json audit-spec`) et validé différentiellement avec repli explicite (`KernelExecutionResult.fallbackDelegated`).
2. **`independent_tested`** : Implémenté indépendamment et validé par l'oracle différentiel et le corpus adversarial.
3. **`delegated_faithful`** :abaissé via [`MediaPlanIR`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L293-L305) et exécuté par délégation structurée (`fork` + `execvp` sans interpolation shell via [`leanav_c_exec_delegated_ffmpeg`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5993-L6040) ou `libav*` lié) avec parité différentielle.
4. **`translated_partial`** : Pipeline de transcodage MP4 pixel/SIMD (`h264`, `hevc`, `av1`, `scale`, `colorspace=bt709`, `tonemap`, `-ss`, `-t`) vérifié par les portes de fidélité visuelle et de synchronisation conteneur.
5. **`approximate`** : Comportement borné par tolérance numérique explicite (PSNR / luma / durée).
6. **`unsupported`** : Rejeté en mode *fail-closed* (code de retour non nul, diagnostic structuré sur `stdout` en mode `-json` ou sur `stderr` hors `-json`, zéro fichier partiel résiduel).
7. **`untested`** : Inventorié dans `declared_ffmpeg_capabilities` mais jamais revendiqué comme supporté.

---

## 2. Synthèse par Phase (Phases 0 à 7)

### Phase 0 (Wave A) — Gouvernance, Registre de Capacités & Référence Épinglée
- **Binaire FFmpeg de référence épinglé** : `6.1.1-3ubuntu5` (`/tmp/opencode/ffmpeg-runtime-full/bin/ffmpeg` et `ffprobe`, hashes SHA-256 enregistrés).
- **Générateur & Registre** : [`scripts/generate_capability_registry.py`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/scripts/generate_capability_registry.py) et [`docs/capability-registry.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/capability-registry.json) séparant strictement `declared_ffmpeg_capabilities` (`inventory_only: true`, 14 domaines complets) et `tested_lean_ffmpeg_capabilities`.
- **Contrats** :
  - [`docs/contracts/platform-qualification.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/platform-qualification.json) (`linux-x86_64` : `tested_local` ; `macos-arm64`, `linux-arm64`, `windows-x86_64` : `untested`).
  - [`docs/contracts/quorum-wave-a.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/quorum-wave-a.json) (validation par quorum externe Fable/Astra/Gemini reportée à la validation finale de fin de campagne sur autorisation explicite de Thomas).

### Phase 1 (Wave A) — Harnais Différentiel Borné & Routage CLI
- **Harnais** : [`tests/differential/runner.py`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/tests/differential/runner.py) avec isolation des répertoires de travail, limites de temps/CPU/mémoire/sortie, terminaison de groupe de processus, normalisation rationnelle `ffprobe`, sondes paquets/frames et sondes décodées.
- **Routage CLI & Hygiène d'Erreur** : [`LeanAV/Cli.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Cli.lean) et [`LeanAV/Main.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Main.lean) garantissant :
  - Exactement un objet JSON sur `stdout` et `stderr == ""` lorsque `-json` / `--json` est activé (succès comme échec, y compris pendant le transcodage H.264/HEVC/AV1).
  - Suppression complète des bannières et statistiques sur `stderr` pour `-v quiet|panic|fatal|error|warning|-8|0|8|16|24`.
  - Suppression automatique (`unlink`) de tout fichier de sortie partiel en cas d'échec de remuxage ou de transcodage sur des médias corrompus ou tronqués.

### Phase 2 (Waves B & C) — Invariants de Base (Temps, Seek, VFR/B-frames, Couleur, Audio, Déterminisme)
- **Contrat** : [`docs/contracts/timing-seek.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/timing-seek.json).
- **Tests différentiels** : [`tests/differential/test_phase2.py`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/tests/differential/test_phase2.py) vérifiant :
  - Le rejet *fail-closed* des entrées manquantes sans artefact.
  - Les métadonnées colorimétriques (`bt709`, `tv`), le format 10 bits `yuv444p10le`, les flux VFR avec B-frames (`nb_frames = 20`, 29 frames décodées), le décompte exact d'échantillons audio (`48000 Hz`, `duration_ts = 96000`), et la reproductibilité bit-exacte (SHA-256 identique sur exécutions répétées).

### Phase 3 (Wave D) — Représentation Intermédiaire Typée (`MediaPlanIR`)
- **Contrat** : [`docs/contracts/phase3-ir-schema.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/phase3-ir-schema.json).
- **Implémentation** : [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean) (`MediaPlanIR`, `parseArgsToPlanIR`, `planIRToCliArgs`, `validatePlanIR`, `serializePlanIRJson`).
- **Inspection CLI** : `lffmpeg plan <args>` et `lffmpeg -dump-plan <args>`.
- **Théorèmes prouvés (`0 sorryAx`)** :
  - [`LeanAV.PlanIR.streamMapSpec_parse_format_roundtrip`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L939-L946)
  - [`LeanAV.PlanIR.planIR_cli_roundtrip_verified`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L980-L994)
  - [`LeanAV.PlanIR.validatePlanIR_sound_and_rejects_unsafe`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1001-L1007)

### Phase 4 (Waves E & F) — Compatibilité Déléguée Générale & Porte de Sécurité Protocoles
- **Contrat** : [`docs/contracts/phase4-delegated-coverage.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/phase4-delegated-coverage.json).
- **Couverture** : Conteneurs `mp4`, `matroska` (`.mkv`), `webm`, `wav`, `flac`, `ogg`, `mpegts` (`.ts`), `ivf`, `adts` (`.aac`), `framecrc`, `md5`, `null` ; options `-map`, `-metadata`, `-map_metadata`, `-map_chapters`, `-c:s` / `-scodec`, `-sn`, `-bsf:v`, `-bsf:a`.
- **Sécurité (§8)** : [`LeanAV.PlanIR.isSafeLocalMediaPath`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L222-L234) et théorème [`LeanAV.PlanIR.protocolSecurityPolicy_accepts_local_and_rejects_network_device_traversal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L964-L973) rejetant `http://`, `https://`, `rtsp://`, `rtmp://`, `tcp://`, `udp://`, `lavfi:`, `concat:`, `/dev/*` et `..`.

### Phase 5 (Wave G) — Façade FFI C-ABI Épinglée, Propriété Mémoire & Annulation
- **Contrat** : [`docs/contracts/phase5-ffi-abi-boundary.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/phase5-ffi-abi-boundary.json).
- **Implémentation C & Lean** :
  - [`leanav_c_ffi_abi_version`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5855-L5858) (`0x00010005`)
  - [`leanav_c_ffi_probe_mp4_contract`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5867-L5969) (zéro allocation, lecture bornée sur `@& ByteArray` emprunté)
  - [`leanav_c_ffi_cancel_gate`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5976-L5985) (barrière atomique `SEQ_CST` + budget de frames)
  - [`leanav_c_verify_plane_ffi_contract`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5826-L5847) (alignement stride 64 octets + padding SIMD de queue de 64 octets)
- **Vérification CLI** : `lffmpeg verify-ffi`.

### Phase 6 (Wave H) — Noyaux Indépendants Vérifiés avec Repli Explicite
- **Contrat** : [`docs/contracts/phase6-independent-kernels.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/phase6-independent-kernels.json).
- **Noyaux qualifiés (`independent_verified`)** :
  1. [`LeanAV.PlanIR.rescalePtsIndependentOrFallback`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L891-L902) (conversion rationnelle exacte de timestamps avec repli explicite hors domaine).
  2. [`LeanAV.PlanIR.scalePlane2x2IndependentOrFallback`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L909-L915) (downscaler 2x2 vérifié avec garde de bornes et parité dimensionnelle).
  3. [`LeanAV.PlanIR.demuxIvfIndependentOrFallback`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L922-L930) (démuxeur conteneur IVF avec vérification d'intégrité 64-bit par paquet).
- **Théorème de complétude et repli** : [`LeanAV.PlanIR.independentKernel_fallback_complete_and_sound`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1014-L1021).
- **Vérification CLI** : `lffmpeg verify-kernels`.

### Phase 7 — Promotion Progressive, Rollback & Clôture
- **Contrat** : [`docs/contracts/phase7-promotion-and-rollback.json`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/docs/contracts/phase7-promotion-and-rollback.json).
- **Politique de Rollback** : Toute régression différentielle, violation FFI ou sortie de domaine déclenche `KernelExecutionResult.fallbackDelegated` vers `BackendTier.delegatedFaithful` ou la rétrogradation immédiate dans le registre de capacités.

---

## 3. Audit par Quorum Externe (3 Modèles : Fable 5.1, Astra, Gemini 4 Argon) & Remédiations

Le quorum des trois modèles a été exécuté via Orb MCP dans leurs harnais respectifs sur le nœud `nippur` :
- **Claude Fable 5.1** (`claudecode`, `claude-fable-5-1`) — Mission `20e7bae7-a9ed-412d-9314-624296673d97`
- **GPT-6 Astra** (`codex`, `gpt-6-astra`) — Mission `667e0fbb-daed-40f3-a989-876e75778181`
- **Gemini 4 Argon** (`antigravity`, `gemini-4-argon`) — Mission `912bb20d-d926-484b-b6e9-f761aa4c61df`

### Synthèse des Correctifs & Simplifications Appliqués suite au Quorum
1. **Parité FFmpeg par flux (`copyWithFilter` et pipelines mixtes copy/encode)** :
   - Validation `copyWithFilter` corrigée par flux (`(vCopy && hasVf) || (aCopy && hasAf)`) dans [`LeanAV/Cli.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Cli.lean#L341-L343) et [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L510-L512).
   - Prise en charge de `-vf scale=... -c:v h264 -c:a copy` et `-c:v copy -c:a aac` via routage `delegatedFaithful` dans [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L525-L534).
2. **Formatage exact des durées fractionnaires (`formatCliSeconds`) & Syntaxe Temporelle** :
   - Correction dans [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L341-L361) (`formatFracDigitsLoop`) préservant les zéros significatifs après la virgule (`-t 0.0050` $\to$ `"0.005"`, `-ss 1.0005` $\to$ `"1.0005"`).
   - Extension de [`parseCliSeconds`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Cli.lean#L140-L186) aux formats `HH:MM:SS[.frac]`, `MM:SS[.frac]`, `<n>ms`, `<n>us` et `<n>s`.
3. **Sélection de pistes (`-map 0`, `-map 0:1`) & Conteneurs (`.mov`, `.m4a`, `.mp3`, `.avi`)** :
   - Ajout de `StreamKind.all` dans [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L77-L163) et prise en charge de `.mov`, `.m4a`, `.mp3`, `.avi`.
4. **Suppression de l'inflation `moov_size` (256 Ko) et préservation des métadonnées en `-c copy` MP4** :
   - Suppression de `-moov_size 262144` et `-map_metadata -1 -map_chapters -1` sur la branche `codec_id_u32 == 0` de [`leanav_c_transcode_mp4_general_verified`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/c/leanav_simd_kernels.c#L5405-L5416).
5. **Durcissement de `isSafeLocalMediaPath` & Hygiène JSON sur fichiers manquants** :
   - Rejet de tout chemin contenant `':'` (`file:`, `pipe:`, `fd:`, `data:`, `crypto:`, `hls:`, `subfile:`), `//` en préfixe (`//dev/null`), `/dev/`, `/proc/`, `/sys/` et `..` dans [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L254-L273).
   - Vérification de `System.FilePath.pathExists` en tête de [`runFFmpegCli`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Main.lean#L1185-L1190) avant toute lecture binaire.
6. **Théorèmes Universels (`∀`) & Déduplication Architecturale** :
   - Ajout des théorèmes universels [`streamKind_roundtrip_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L971-L974), [`subtitleCodec_roundtrip_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L979-L982), [`validatePlanIR_sound_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1035-L1044), [`specFfiCancelGate_iff_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1065-L1067), [`rescalePtsIndependentOrFallback_negative_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1072-L1076) et [`cliSecondsToMillis_zero_den_universal`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Cli.lean#L618-L620).
   - Unification de `planIRToCliArgs` et `buildDelegatedFfmpegArgv` via [`renderPlanIRArgv`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L600-L685) et déduplication de `jsonEscape` et du parsing CLI dans `Main.lean`.

---

## 4. Campagne Différentielle & FATE Exhaustive (`445` tests) et Durcissement Maxwell / `lean-native`

### 4.1 Résultats Vérifiés Avant / Après Correctifs (`445` tests)

| Suite de Vérification | Périmètre | Avant (`v0.2.0-quorum`) | Après (`80f1959`) | Détails Vérifiables |
| :--- | :--- | :---: | :---: | :--- |
| **Suite #0 (`tests/`)** | **59 tests** unitaires & différentiels Python + auto-tests C-ABI | `58 / 59` (`98.3%`) | **`59 / 59` (`100%`)** | `15/15` unitaires + `44/44` différentiels + `53/53` waves `self-test` + `15/15` portes C-ABI |
| **Suite #1 (`bench.py`)** | **120 cas** : conteneurs, `-map`, métadonnées, chapitres, dispositions, BSFs, sous-titres, multi-input & timeline | `78 / 120` (`65.0%`) | **`119 / 120` (`99.2%`)** | `111 MATCH` bit-exact + `5 MATCH(lossy)` + `3 MATCH(both-fail)` |
| **Suite #2 (`test_diff.py`)** | **79 cas** : codecs vidéo/audio, `-vf` / `-af`, `pix_fmt`, contrôle de débit (`-crf`, `-b:v`, `-qp`) & découpe temporelle | `41 / 79` (`51.9%`) | **`79 / 79` (`100%`)** | `79/79` codes retour identiques, `79/79` signatures `ffprobe` identiques (`0 DIFF`) |
| **Suite #3 (`fate-run.sh`)** | **187 tests FATE officiels FFmpeg** (`fate-lavf-*` + `fate-ffmpeg-*`) | `0 / 187` FATE pass (`187/187` rejets CLI) | **`129 / 129` FATE pass (`100%`)**<br>**`186 / 186` sorties identiques** | `100%` des `129` tests FATE passés par `ffmpeg 6.1.1` passent avec `lffmpeg`, `0/187` rejet CLI, `186/186` sorties non-vides identiques bit-à-bit |

### 4.2 Durcissement Déclaratif de `AVGateSpec` & Déduplication `LNIR_WIRE_V1`
- **Élimination des 10 spécifications réflexives `gate x = true`** dans [`LeanAV/Spec.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Spec.lean) et [`LeanAV/Domain.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/Domain.lean) au profit de conjonctions propositionnelles déclaratives (`Prop`) et preuves bidirectionnelles (`sound`, `complete`).
- **Audit Zero-Trust (`turbo-lean --json audit-spec`)** : **`118 / 118` spécifications certifiées `non_vacuous_and_tight` (`0` `vacuous`, `0` `trivial`, `0 sorryAx`)** sur `Spec.lean`, `Domain.lean`, `PlanIR.lean`, `NativeKernels.lean`, `Format.lean`, `Scale.lean` et `Filter.lean`.
- **Déduplication de [`LeanAV/NativeKernels.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/NativeKernels.lean)** : réduction de **`1 038` lignes (`-60%`)** via les constructeurs paramétrés `mkLnirFmaDecl` / `mkLnirStencil3Decl` / `mkLnirSaxpyDecl` et la spécification canonique `leanSpecFmaBlend3`.
- **Accélération du réducteur kernel Lean 4 (`whnf`) dans [`LeanAV/PlanIR.lean`](file:///var/lib/sandboxed-node/e9e27628-66ad-4877-bee4-d96c0591d46f/lean-ffmpeg/LeanAV/PlanIR.lean#L1026-L1086)** : élimination `casesOn` en tête réduisant la vérification de `planIR_cli_roundtrip_verified` de `> 40 000 ms` à **`30 ms` (`1 330x` plus rapide)**.
