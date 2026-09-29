# Pluck

A background eraser that runs in your browser. Open a photo, brush away what you don't want, and download a PNG at the photo's original resolution.

Your photo stays on your device. Nothing is uploaded.

## Tools

- **Erase** and **Restore**: paint pixels away or bring them back from the original. Size, hardness and strength are adjustable.
- **Auto**: finds the main subject and removes either the background or the subject. The outline is snapped to real edges in the photo, so hair and thin shapes stay intact.
- **Sniper**: click a color to erase it, either the connected area or every match in the photo. Colors are compared in CIELAB, so the tolerance slider tracks what your eye sees. There is also a brush mode that erases only the target color under the brush.
- **Move**: pan around the photo. Hold Space to pan with any tool, or use two fingers on a touch screen.

You can hold `\` to compare with the original, trim empty edges on download, and undo any step.

Pluck opens JPG, PNG, WebP, AVIF, GIF and BMP files up to 60 megapixels. Drop a file on the page, paste one from the clipboard, or pick one with Open.

## Running it

There is no build step. Serve the folder with any static server and open it in a browser:

```sh
python3 -m http.server 8000
```

Then go to `http://localhost:8000`.

You can also open `index.html` directly, but the browser won't cache the Auto model from a `file://` address, so it downloads again every session.

## Keyboard shortcuts

| Key | Action |
|---|---|
| `E` `R` `A` `S` `H` | Erase, Restore, Auto, Sniper, Move |
| `Space` (hold) | Pan with any tool |
| `[` `]` | Brush size down, up |
| `\` (hold) | Show the original |
| `0` / `1` | Fit to screen / 100% zoom |
| `+` `-` | Zoom in, out |
| `Ctrl+Z` / `Ctrl+Shift+Z` or `Ctrl+Y` | Undo / redo |
| `Ctrl+O` / `Ctrl+S` | Open a photo / download PNG |

On macOS, use `Cmd` in place of `Ctrl`.

## How Auto works

The first time you use Auto, Pluck downloads [RMBG-1.4](https://huggingface.co/briaai/RMBG-1.4) (about 44 MB) from Hugging Face and caches it in the browser. It runs locally with [ONNX Runtime Web](https://onnxruntime.ai/), using WebGPU when available. Later runs load the model from the cache.

RMBG-1.4 is made by BRIA AI and has its own license, separate from this project's. It allows non-commercial use only. If you want to use Auto commercially, check the [model's license](https://huggingface.co/briaai/RMBG-1.4) first.

## License

The code in this repository is released under the [MIT License](LICENSE). The license does not cover the RMBG-1.4 model, which is downloaded at runtime and never included in this repository.
