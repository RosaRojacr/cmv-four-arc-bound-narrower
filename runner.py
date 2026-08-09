"""Run Lean 4 files in a Lake project from Python.

Usage from a notebook:

    from runner import Runner
    Runner.run("Test.lean")

Assumes runner.py sits in the Lake project root (next to lakefile.toml).
Point it elsewhere with Runner.project = "/some/other/path" if not.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path


class Runner:
    # Defaults to the directory containing this file.
    project: Path = Path(__file__).resolve().parent

    @staticmethod
    def _lake() -> str:
        """Find lake, falling back to the standard elan location.

        Jupyter kernels often don't inherit elan's PATH edits, which is the
        usual cause of 'lake: command not found' from a notebook.
        """
        found = shutil.which("lake")
        if found:
            return found
        elan = Path.home() / ".elan" / "bin" / "lake"
        if elan.exists():
            return str(elan)
        raise FileNotFoundError(
            "Could not find `lake`. Install elan, or set Runner.lake_path."
        )

    lake_path: str | None = None

    @classmethod
    def run(cls, filename: str, quiet: bool = False) -> bool:
        """Type-check a Lean file. Returns True if it compiled cleanly.

        Prints Lean's diagnostics (errors, warnings, #eval / #check output,
        `exact?` suggestions). An empty output with exit 0 means success --
        that is what a clean Lean file looks like.
        """
        proj = Path(cls.project).resolve()

        if not (proj / "lakefile.toml").exists() and not (
            proj / "lakefile.lean"
        ).exists():
            print(f"! No lakefile in {proj} -- is this a Lake project root?")
            return False

        target = proj / filename
        if not target.exists():
            print(f"! No such file: {target}")
            leans = sorted(p.name for p in proj.glob("*.lean"))
            if leans:
                print("  Available here:", ", ".join(leans))
            return False

        lake = cls.lake_path or cls._lake()

        result = subprocess.run(
            [lake, "env", "lean", filename],
            cwd=proj,
            capture_output=True,
            text=True,
            env={**os.environ, "PATH": f"{Path(lake).parent}:{os.environ.get('PATH','')}"},
        )

        out = (result.stdout or "") + (result.stderr or "")
        out = out.strip()

        if not quiet:
            if out:
                print(out)
            if result.returncode == 0:
                warned = "warning:" in out
                print(f"\n[ok] {filename} compiled" + (" with warnings" if warned else ""))
            else:
                print(f"\n[fail] {filename} -- exit {result.returncode}")

        return result.returncode == 0

    @classmethod
    def build(cls, quiet: bool = False) -> bool:
        """Run `lake build` on the whole project, respecting the import graph."""
        proj = Path(cls.project).resolve()
        lake = cls.lake_path or cls._lake()
        result = subprocess.run(
            [lake, "build"], cwd=proj, capture_output=True, text=True
        )
        if not quiet:
            print((result.stdout or "") + (result.stderr or ""))
        return result.returncode == 0

    SMOKE_TEST = """import Mathlib

-- 1. evaluation
#eval 2 + 2

-- 2. Mathlib loaded
#check Real.pi

-- 3. elaboration + ring
example (a b : \u211d) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- 4. numeric bounds on pi  (needed for the certificate section)
example : (3.14 : \u211d) < Real.pi := by exact Real.pi_gt_d2

-- 5. derivatives  (needed for the arc' identity)
example : deriv (fun x : \u211d => x^2) 1 = 2 := by simp
"""

    @classmethod
    def test(cls, filename: str = "SmokeTest.lean", keep: bool = True) -> bool:
        """Write and check a known-good file exercising the toolchain.

        Confirms Mathlib imports and that `ring`, `simp`, `deriv` and the pi
        bounds all elaborate. Use after a toolchain or Mathlib update, or when
        a real proof fails in a way that might not be the proof's fault.

        Overwrites `filename`; pass keep=False to delete it afterwards.
        """
        proj = Path(cls.project).resolve()
        target = proj / filename
        target.write_text(cls.SMOKE_TEST)
        try:
            ok = cls.run(filename, quiet=True)
            if ok:
                print("[ok] toolchain healthy -- Mathlib, ring, simp, deriv, pi bounds")
            else:
                print("[fail] smoke test did not compile:\n")
                cls.run(filename)
                print(
                    "\nIf a lemma name is unknown, Mathlib has renamed it. "
                    "Replace the tactic with `exact?` and read the `Try this:` line."
                )
            return ok
        finally:
            if not keep:
                target.unlink(missing_ok=True)

    @classmethod
    def write(cls, filename: str, source: str, run: bool = True) -> bool:
        """Write a Lean file from a Python string, then optionally check it.

        Handy for the numerics-to-Lean loop: compute a constant with mpmath,
        interpolate it into a Lean statement, check it immediately.
        """
        proj = Path(cls.project).resolve()
        (proj / filename).write_text(source)
        return cls.run(filename) if run else True
    @classmethod
    def add_root(cls, name: str) -> None:
        """Add a module to lakefile roots if absent, then build it."""
        import re
        proj = Path(cls.project).resolve()
        lf = proj / "lakefile.toml"
        txt = lf.read_text()
        m = re.search(r'^roots = \[(.*?)\]', txt, re.M)
        if m and f'"{name}"' not in m.group(1):
            new = m.group(0)[:-1] + f', "{name}"]'
            lf.write_text(txt.replace(m.group(0), new))
            print(f"added {name} to roots")
        subprocess.run([cls.lake_path or cls._lake(), "build", name], cwd=proj)

