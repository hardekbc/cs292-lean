#!/usr/bin/env python3
# use comparator to check Lean submissions

import json
import subprocess
import sys
import glob
import os

from os.path import basename
from typing import Dict, List, Any, Tuple

# root directory for autograding, useful for testing the autograder.
root_dir = "/autograder"

# where the autograder source files (including this script) are located.
source_dir = f"{root_dir}/source"

# where the student's submitted files are located, provided by gradescope.
student_submission_dir = f"{root_dir}/submission"

# where the grader output needs to go for gradescope to see it.
results_file = f"{root_dir}/results/results.json"

# location of the `lake` executable
lake_bin = "/root/.elan/bin"

# the data structure to be written out to 'results_file'. it's format (ignoring
# optional fields that we don't need):
#
# {
#   'score': <the overall score for the assignment>,
#   'tests': [
#     {
#       'name': <description>,
#       'status': <passed | failed>,
#       'output': <summary of results>,
#     },
#     ...
#   ]
# }
results: Dict[str, List[Dict[str, Any]]] = {
    "score": 0,
    "tests": [],
}


# bails out of the grader early with an error message
def Bail(msg: str):
    print(f"bailing: {msg}")
    results["output"] = msg
    with open(results_file, "w") as out:
        out.write(json.dumps(results))
    sys.exit(0)


# bails iff the command output is an error
def BailOnFailure(cmd_out, msg: str):
    if not cmd_out[0]:
        Bail(msg + "\n" + cmd_out[1])


# runs the specified command in the shell
def Run(cmd: str) -> Tuple[bool, str]:
    print(f"Run: {cmd}")
    proc = subprocess.run(
        cmd,
        shell=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )

    # collect the output
    output = proc.stdout + b"\n"

    if proc.returncode != 0:  # error
        output += proc.stderr
        return (False, output.decode("utf-8"))
    else:
        return (True, output.decode("utf-8"))


# run command and bail on failure
def RunOrBail(cmd: str) -> str:
    result = Run(cmd)
    BailOnFailure(result, "")
    return result[1]


# write out a Comparator config.json for the given theorem
def WriteConfig(thm: str):
    config: Dict[str, List[Dict[str, Any]]] = {
        "challenge_module": "Ref",
        "solution_module": "Submission",
        "theorem_names": [thm],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": False,
    }
    with open("config.json", "w") as out:
        out.write(json.dumps(config))


# extract the reason for a Comparator failure from its output
def ExtractReason(error: str) -> str:
    if error.find("Illegal axiom detected"):
        if error.find("sorryAx"):
            return "uses `sorry`"
        else:
            return "uses illegal axiom"
    elif (
        error.find("theorem statement do not match")
        or error.find("constant kind don't match")
        or error.find("does not match between challenge and target")
        or error.find("is not a theorem")
        or error.find("is not a definition")
    ):
        return "proves incorrect statement"
    elif error.find("Child exited with"):
        return "failed to build"
    elif error.find("Running Lean default kernel on solution") and not error.find(
        "Lean default kernel accepts the solution"
    ):
        return "Lean kernel rejected the solution"
    else:
        return "unknown reason"


# grade a specific theorem
def Grade(thm: str):
    print(f"Grade: {thm}")
    WriteConfig(thm)
    result = Run(
        f"COMPARATOR_LANDRUN=$(realpath .lake/packages/comparator/scripts/fake-landrun.sh) COMPARATOR_LEAN4EXPORT=$(realpath .lake/packages/lean4export/.lake/build/bin/lean4export) {lake_bin}/lake env .lake/packages/comparator/.lake/build/bin/comparator config.json"
    )

    # abnormal exit
    if not result[0]:
        results["tests"].append(
            {
                "name": thm,
                "status": "failed",
                "output": ExtractReason(result[1]),
            }
        )
    else:
        results["score"] += 1
        results["tests"].append(
            {
                "name": thm,
                "status": "passed",
            }
        )


# get the submitted Lean file's name
def GetSubmittedFilename() -> str:
    files = glob.glob(f"{student_submission_dir}/*.lean")
    if len(files) != 1:
        Bail("exactly one *.lean file should be submitted")
    return basename(files[0])


# prep
os.chdir(source_dir)  # just to be sure
file = GetSubmittedFilename()
RunOrBail(f"cp {student_submission_dir}/{file} {source_dir}/Submission.lean")
RunOrBail(f"cp {source_dir}/Course/Exercises/{file} {source_dir}/Ref.lean")

# do testing
thms = RunOrBail(f"cat {source_dir}/theorem_names.txt").split()
for thm in thms:
    Grade(thm)

# write out the final results
with open(results_file, "w") as out:
    out.write(json.dumps(results))
