## TilingPolyomino

Formal proofs in Lean about tilings of regions by polyominoes.

The project currently focuses on tilings of rectangles by trominoes, starting from the classical theorem of Ash and Golomb, and is intended as a growing collection of formalized results on tilings by various polyominoes.

The initial development is based on:

> J. Marshall Ash and Solomon W. Golomb,  
> **Tiling Deficient Rectangles with Trominoes**,  
> *Mathematics Magazine* **77** (2004), no. 1, 46–55.  
> [doi: 10.2307/3219230](https://dx.doi.org/10.2307/3219230)

An earlier preprint version is available at  
[https://condor.depaul.edu/mash/tilerec2a.pdf](https://condor.depaul.edu/mash/tilerec2a.pdf),  
where some theorem names (for example the “DOG-EARED RECTANGLE THEOREM”) differ slightly
from the final published article.

Future work will extend this library with additional theorems and constructions about tilings by trominoes and other polyominoes.

---

## Project structure

- `TilingPolyomino.lean`: main entry point for the library.
- `TilingPolyomino/Basic.lean`: basic definitions and helper lemmas.
- `TilingPolyomino/LTromino.lean`: development around tilings with L‑trominoes and related results inspired by Ash–Golomb.

---

## Requirements

This project uses the Lean theorem prover and its package manager Lake.

- **Lean**: see the version in `lean-toolchain`.
- **Lake**: comes bundled with recent Lean installations.

If you have Lean installed via elan, the correct version will be selected automatically when you run commands in this directory.

---

## Building and running

From the project root (`TilingPolyomino/` directory that contains `lakefile.toml`), run:

```bash
lake build
```

To open the project in an editor (such as VS Code) with Lean support, simply open this directory and start the Lean language server; it will read `lean-toolchain` and fetch any required dependencies.

You can also run the default Lake script (if any are defined) with:

```bash
lake run
```

---

## Using the library

Once the project is built, you can import its main namespace in your own Lean files with:

```lean
import TilingPolyomino
```

or, for more specific components:

```lean
import TilingPolyomino.LTromino
```

The goal is to provide reusable definitions and theorems about tilings by polyominoes, so that further results can build on a common foundation.

---

## Contributing

Contributions that extend the library with new tiling results, additional polyomino classes, or improved proofs and documentation are welcome.

Possible directions include (but are not limited to):

- New theorems about tilings of rectangles and other regions by trominoes and higher-order polyominoes.
- Formalization of existing results in the tiling literature.
- General infrastructure and abstractions for working with polyominoes and tilings in Lean.

Please feel free to open issues or pull requests on GitHub with ideas, questions, or proposed additions.

---

## License

Unless otherwise stated, this project is made available under an open-source license compatible with typical Lean community projects. See the `LICENSE` file if present, or the GitHub repository page, for precise licensing information.