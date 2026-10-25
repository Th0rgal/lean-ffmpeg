# lean-ffmpeg (`LeanAV`)

Implémentation formellement vérifiée en **Lean 4** (`v4.31.0`) d'un pipeline multimédia et d'une façade CLI compatible `ffmpeg` (`lffmpeg`), compilée vers C natif / SIMD / GPU (`LNIR_WIRE_V1`) avec **`0 sorryAx`** et auditée par l'oracle Zero-Trust **`turbo-lean`**.

---

## Architecture en 4 Niveaux de Qualification (`MediaPlanIR`)

Chaque requête CLI est analysée dans une représentation intermédiaire typée (`MediaPlanIR` dans `LeanAV/PlanIR.lean`), validée par une politique de sécurité **fail-closed** (rejet formellement prouvé des protocoles réseau, périphériques `/dev/*` et traversées `..`), puis routée vers l'un des 4 niveaux :

| Niveau | Rôle | Exemples |
| :--- | :--- | :--- |
| **`independent_verified`** | Noyaux Lean 4 + C-ABI SIMD prouvés sans dépendance FFmpeg, avec repli explicite (`fallbackDelegated`) | Downscale 2×2 / 3:2 (`scale`), prédicteur/décodeur LPC FLAC Ordre-4, CDEF/Wiener AV1, SAO HEVC, démux/mux MP4 & IVF natifs, arithmétique exacte `AVRational` |
| **`translated_partial`** | Orchestration C-ABI directe (`libavformat` / `libavcodec` / `libswscale`) vérifiée par portes C-ABI | Transcodage MP4 (`h264`, `hevc`, `av1`, `aac`, `-ss`, `-t`, `-vf scale/crop/boxblur/unsharp/eq`), probe JSON |
| **`delegated_faithful`** | Exécution structurée `fork`/`execvp` (sans interpolation shell) vers `ffmpeg` | Conteneurs `.mkv`, `.webm`, `.mov`, `.wav`, `.flac`, `.ogg`, `.ts`, `.avi`, `.ast`, `-map`, `-metadata`, `-disposition`, `-bsf`, `-filter_complex` |
| **`unsupported`** | Rejet déterministe avec diagnostic explicite et zéro fichier partiel | Protocoles non sûrs (`http://`, `rtsp://`, `pipe:`, `/dev/*`, `..`), combinaisons invalides (`-c:v copy -vf ...`) |

---

## Parité Différentielle & FATE Vérifiée face à `ffmpeg 6.1.1` (`445` tests)

| Suite de Vérification | Périmètre | Résultat Vérifié | Détails |
| :--- | :--- | :---: | :--- |
| **Suite #0 (`tests/`)** | **59 tests** unitaires & différentiels Python + auto-tests C-ABI | **`59 / 59` (`100%`)** | `15/15` unitaires + `44/44` différentiels + `53/53` waves `self-test` + `15/15` portes C-ABI |
| **Suite #1 (`bench.py`)** | **120 cas** : conteneurs, `-map`, métadonnées, chapitres, dispositions, BSFs, sous-titres, multi-input & timeline | **`119 / 120` (`99.2%`)** | `111 MATCH` bit-exact + `5 MATCH(lossy)` + `3 MATCH(both-fail)` |
| **Suite #2 (`test_diff.py`)** | **79 cas** : codecs vidéo/audio, `-vf` / `-af`, `pix_fmt`, contrôle de débit (`-crf`, `-b:v`, `-qp`) & découpe temporelle | **`79 / 79` (`100%`)** | `79/79` codes retour identiques, `79/79` signatures `ffprobe` identiques (`0 DIFF`) |
| **Suite #3 (`fate-run.sh`)** | **187 tests FATE officiels FFmpeg** (`fate-lavf-*` + `fate-ffmpeg-*`) | **`129 / 129` FATE pass (`100%`)**<br>**`186 / 186` sorties identiques** | `100%` des `129` tests FATE passés par `ffmpeg 6.1.1` passent avec `lffmpeg`, `0/187` rejet CLI, `186/186` sorties non-vides identiques bit-à-bit |

---

## Spécifications Formelles Déclaratives (`AVGateSpec`) & Audit Zero-Trust (`turbo-lean`)

Chaque porte de sécurité et de conformité implémente la méta-spécification [`AVGateSpec`](LeanAV/Spec.lean) reliant une porte exécutable C-ABI (`UInt8`) à un prédicat déclaratif `Prop` indépendant (`sound`, `complete`, `posWitness`, `negWitness`, `nonVacuous`, `tight`) :

| Module Audité (`turbo-lean --json audit-spec`) | Spécifications `non_vacuous_and_tight` | `vacuous` | `trivial` | `sorryAx` | Temps |
| :--- | :---: | :---: | :---: | :---: | ---: |
| `LeanAV/Spec.lean` (9 portes `AVGateSpec` + 5 lois) | **`23 / 23` (`100%`)** | `0` | `0` | `0` | `10.4 ms` |
| `LeanAV/Domain.lean` (`FFmpegAcceptanceSafe` + pistes) | **`8 / 8` (`100%`)** | `0` | `0` | `0` | `8.9 ms` |
| `LeanAV/PlanIR.lean` (`MediaPlanIR` + sécurité + FFI) | **`11 / 11` (`100%`)** | `0` | `0` | `0` | `10.0 ms` |
| `LeanAV/NativeKernels.lean` (50 waves `LNIR_WIRE_V1`) | **`19 / 19` (`100%`)** | `0` | `0` | `0` | `9.7 ms` |
| `LeanAV/Format.lean` (ISOBMFF / MP4 / FLAC / ADTS / Opus) | **`45 / 45` (`100%`)** | `0` | `0` | `0` | `14.5 ms` |
| `LeanAV/Scale.lean` & `LeanAV/Filter.lean` | **`12 / 12` (`100%`)** | `0` | `0` | `0` | `12.5 ms` |

---

## Compilation & Vérification

```bash
# Compiler le projet et les preuves formelles (70 cibles Lake, 0 sorryAx)
lake build

# Exécuter les 53 vagues d'auto-tests formels et les 15 portes C-ABI
./.lake/build/bin/lffmpeg self-test

# Vérifier les contrats C-ABI et les noyaux indépendants avec repli prouvé
./.lake/build/bin/lffmpeg verify-ffi
./.lake/build/bin/lffmpeg verify-kernels

# Auditer les spécifications formelles avec turbo-lean (0 vacuous, 0 trivial)
turbo-lean --json audit-spec LeanAV/Spec.lean

# Suite de tests unitaires et différentiels Python (59 tests)
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_phase*.py"
```

---

## Benchmarks Comparatifs : `lffmpeg` vs `ffmpeg` (`6.1.1`)

Mesures effectuées sur Linux x86\_64 (médiane sur 7 exécutions après warmup) sur une source MP4 **1080p** (`1920x1080`, 120 frames, 4.0 s, H.264 + AAC, `7.65 Mo`) et sur les noyaux en mémoire :

### 1. CLI de bout en bout (`lffmpeg` vs `ffmpeg 6.1.1-3ubuntu5`)

| Opération CLI | `ffmpeg 6.1.1` | `lffmpeg` | Ratio | Détails d'exécution |
| :--- | ---: | ---: | ---: | :--- |
| **Remux MKV (`-map` + `-metadata -c copy`)** | `81.5 ms` | `86.1 ms` | `1.06x` | Validation `MediaPlanIR` + délégation `execvp` (`7.83 Mo` identiques) |
| **Extraction audio WAV (`-vn -c:a pcm_s16le`)** | `74.4 ms` | `82.1 ms` | `1.10x` | Sortie bit-exacte (`385 102 octets`) |
| **Extraction audio FLAC (`-vn -c:a flac`)** | `82.3 ms` | `90.6 ms` | `1.10x` | Sortie bit-exacte (`231 784 octets`) |
| **Stream copy MP4 1080p (`-c copy`, 7.65 Mo)** | `71.6 ms` | `81.4 ms` | `1.14x` | Probe zéro-copie `pread` + remux `libavformat` sans inflation `moov` |
| **Stream copy MP4 320×240 (`-c copy`, fixture)** | `62.7 ms` | `72.2 ms` | `1.15x` | Sortie `22.5 Ko` (identique à `ffmpeg`, métadonnées préservées) |
| **Scale 1080p → 540p + H.264 (`-vf scale=960:540`)** | `496.0 ms` | `912.0 ms` | `1.84x` | Probe formel + pipeline C-ABI `libavcodec`/`libswscale` |
| **Seek + Trim (`-ss 1.0 -t 2.0` H.264 + AAC)** | `407.2 ms` | `932.5 ms` | `2.29x` | Décodage/ré-encodage borné par timestamps exacts `AVRational` |

### 2. Noyaux natifs vérifiés (`independent_verified`, in-process)

| Noyau / Pipeline (`lffmpeg bench*`) | `ffmpeg 6.1.1` | `lffmpeg` | Débit / Latence `lffmpeg` |
| :--- | ---: | ---: | :--- |
| **Downscale 4K → 1080p (8 frames `3840x2160`)** | `111.32 ms` (`72 fps`) | **`3.24 ms`** | **`2 471 fps`** (`IO.asTask` 4 workers, tuiles disjointes zéro-copie) |
| **Downscale 4K → 1080p SIMD 1-thread (8 frames)** | `111.32 ms` (`72 fps`) | **`8.85 ms`** | **`904 fps`** (`leanav_simd_scale_2x2_u8`) |
| **Downscale 1080p → 720p SIMD 3:2 (8 frames)** | — | **`7.86 ms`** | **`1 018 fps`** (`leanav_simd_scale_3to2_u8`) |
| **Pipeline D complet (4K → 1080p + mux MP4, 8 frames)** | — | **`41.07 ms`** | **`194 fps`** (`5.13 ms/frame`, vérification en boucle incluse) |
| **Démuxeur MP4 zéro-copie (`1 000` itérations)** | — | **`88 µs`** | **`0.088 µs / itération`** (`11.3 M ops/s`) |
| **Roundtrip FLAC LPC Ordre-4 (`1 000` itérations)** | — | **`52 µs`** | **`0.052 µs / itération`** (`19.2 M ops/s`, sans perte) |

---

## Structure du Dépôt

- `LeanAV/` : Spécifications déclaratives et théorèmes universels (`0 sorryAx`, `118/118` specs `non_vacuous_and_tight`) — `Spec.lean`, `Domain.lean`, `Core.lean`, `Format.lean`, `Video.lean`, `Audio.lean`, `Scale.lean`, `Filter.lean`, `Encoder.lean`, `NativeKernels.lean`, `Cli.lean`, `PlanIR.lean`, `Main.lean`.
- `c/leanav_simd_kernels.c` : Noyaux SIMD C-ABI (`AVX2` / `NEON`), façade `libavformat`/`libavcodec`/`libswscale` et exécution déléguée `execvp` sans shell.
- `tests/` : Suite de tests unitaires et différentiels (`59` tests Python) face à `ffmpeg`/`ffprobe`.
- `docs/` : Plan Maxwell (`FFMPEG_PARITY_MAXWELL_PLAN.md`), registre de capacités (`capability-registry.json`), contrats (`docs/contracts/`) et dossier de clôture (`CAMPAIGN_CLOSURE_DOSSIER.md`).
