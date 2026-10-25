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
