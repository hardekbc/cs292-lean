# CS 292C Intro to the Lean Interactive Theorem Prover

Prof. Ben Hardekopf
UCSB Computer Science Dept

## Goal

The goal of this course is to provide an introduction to modeling and proving
properties of formalized systems using Lean, and to be suitable as a foundation
for Computer Science students who wish to apply Lean to their own work.

## Prerequisites

The course material assumes that the use has programming experience (but not
necessarily _functional_ programming experience) and a basic knowledge of logic
and proofs (e.g., as would be covered in an introductory discrete math course).

## Installation Instructions
### Installing Lean

1. Install Visual Studio Code (https://code.visualstudio.com/).

2. Open VS Code and go to the Extensions marketplace by clicking on the appropriate icon on the left-hand side menu (or typing `Ctrl-Shift-X`).

3. Find the official Lean 4 extension by typing "lean 4" into the search bar; its name is "Lean 4".

4. Install the Lean 4 extension, following the built-in Lean setup guide.

### Installing the course repo

1. Go to the repo's Github page at https://github.com/hardekbc/cs292-lean/.

2. Download the repo by clicking on the green Code button and selecting `Download ZIP`.

3. Unzip the downloaded file.

4. Change into the course directory and type `lake exe cache get` on the command-line to download the Mathlib cache of compiled files (skipping this step will mean that VS Code will automatically download and compile Mathlib from scratch when you open one of the Lean files in the repo, which can take a long time).

5. Open VS Code from the course directory by typing `code .`
