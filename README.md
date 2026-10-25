# lean-ffmpeg (`LeanAV`)

Implémentation formellement vérifiée en **Lean 4** (`v4.31.0-nightly`) d'un pipeline multimédia et d'une façade CLI compatible `ffmpeg` (`lffmpeg`), compilée vers C natif / SIMD avec **0 `sorryAx`** et auditée par `turbo-lean`.

---

## Architecture en 4 Niveaux de Qualification

Chaque requête CLI est compilée vers une représentation intermédiaire typée (`MediaPlanIR` dans `LeanAV/PlanIR.lean`), validée par une politique de sécurité **fail-closed** (rejet prouvé des protocoles réseau, périphériques et traversées `..`), puis routée vers l'un des 4 niveaux :

| Niveau | Rôle | Exemples |
| :--- | :--- | :--- |
| **`independent_verified`** | Noyaux Lean 4 + C-ABI SIMD prouvés sans dépendance FFmpeg | Downscale 2×2 (`scale`), prédicteur/décodeur LPC FLAC Ordre-4, CDEF AV1, démux/mux MP4 natif, arithmétique `AVRational` |
| **`translated_partial`** | Orchestration C-ABI directe (`libavformat` / `libavcodec` / `libswscale`) | Transcodage MP4 (`h264`, `aac`, `-ss`, `-t`, `-vf scale=W:H`), probe JSON |
| **`delegated_faithful`** | Exécution structurée `fork`/`execvp` (sans shell) vers `ffmpeg` | Conteneurs `.mkv`, `.webm`, `.mov`, `.wav`, `.flac`, `.ogg`, `.ts`, `-map`, `-metadata`, `-vn`/`-an` |
| **`unsupported`** | Rejet déterministe avec diagnostic explicite (code `1`) | Chemins non sûrs (`http://`, `..`), filtres ou codecs invalides |

---

## Compilation & Vérification

```bash
# Compiler le projet et les preuves formelles (70 cibles Lake, 0 sorryAx)
lake build

# Exécuter les 53 vagues d'auto-tests formels et les 15 portes C-ABI
./.lake/build/bin/lffmpeg self-test

# Vérifier les 6 contrats C-ABI et les noyaux indépendants
./.lake/build/bin/lffmpeg verify-ffi tests/differential/fixtures/input-av.mp4
./.lake/build/bin/lffmpeg verify-kernels

# Suite de tests différentiels et de registre Python (59 tests)
python3 -m unittest discover -s tests -p "test_*.py"
python3 -m unittest discover -s tests/differential -p "test_*.py"
```

---

## Utilisation CLI (`lffmpeg`)

```bash
# Transcodage H.264 + redimensionnement (ou copie audio -c:a copy)
./.lake/build/bin/lffmpeg -y -i input.mp4 -vf scale=960:540 -c:v h264 -preset ultrafast -crf 23 -c:a copy output.mp4

# Remux MKV/MOV avec sélection de pistes (-map 0 ou -map 0:v:0) et métadonnées
./.lake/build/bin/lffmpeg -y -i input.mp4 -map 0:v:0 -map 0:a:0 -metadata title="LeanAV" -c copy output.mkv

# Inspecter le plan d'exécution vérifié (MediaPlanIR en JSON)
./.lake/build/bin/lffmpeg plan -i input.mp4 -vf scale=640:360 -c:v h264 output.mp4

# Probe JSON déterministe d'un conteneur
./.lake/build/bin/lffmpeg probe input.mp4
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

- `LeanAV/` : Spécifications et théorèmes universels (`0 sorryAx`, `0` alerte `turbo-lean`) — `Core.lean`, `Format.lean`, `Video.lean`, `Audio.lean`, `Filter.lean`, `Encoder.lean`, `Spec.lean`, `Cli.lean`, `PlanIR.lean`, `Main.lean`.
- `c/leanav_simd_kernels.c` : Noyaux SIMD C-ABI, façade `libavformat`/`libavcodec`/`libswscale` et exécution déléguée `execvp` sans shell.
- `tests/` : Suite de tests unitaires et différentiels (`59` tests Python) face à `ffmpeg`/`ffprobe`.
- `docs/` : Plan Maxwell (`FFMPEG_PARITY_MAXWELL_PLAN.md`), registre de capacités (`capability-registry.json`), contrats (`docs/contracts/`) et dossier de clôture (`CAMPAIGN_CLOSURE_DOSSIER.md`).
