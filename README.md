# XACQ/XDCA: Precondition Constraint Acquisition Using Path Predicates

XACQ/XDCA performs precondition inference relying on constraint acquisition and path predicates. XACQ/XDCA does not need the source code of the function under analysis, only the binary.
XACQ/XDCA is part of the BINSEC toolbox for binary-level program analysis and is built on top of the [constraint acquisition platform](https://github.com/lirmm/ConstraintAcquisition).

The tool provides four acquisition algorithms:

| Algorithm | Config / `bench.py` options |
|-----------|-----------------------------|
| CONACQ    | `algo: conacq` / `--algo conacq` |
| XACQ      | `algo: conacq` + `explain: true` / `--algo conacq --explain` |
| DCA       | `algo: dca` / `--algo dca` |
| XDCA      | `algo: dca` + `explain: true` / `--algo dca --explain` |

# Table of Contents

1. [Quick Setup - Docker Image](#docker_image)
2. [Requirements](#requirements)
3. [Installation](#installation)
4. [Usage](#usage)
5. [Experiments](#experiments)
    1. [RuleML+RR](#ruleml)
    2. [Constraints Journal](#journal)

<a name="docker_image"></a>
# Quick Setup - Docker Image (XACQ only)

You do not need to clone this GitHub repository or download any source code to use XACQ. As long as you have Docker installed, you can run the tool directly from your terminal. Docker will automatically download the image from the registry the first time you execute it.
```shell
sudo docker pull sdjebour/xacq:latest
sudo docker run --rm -it --user opam sdjebour/xacq:latest
```
When entering the Docker container, you must initialize the OCaml environment by running:
```shell
eval $(opam env)
```
All set! You can now proceed to the Usage and Experiments sections below.

<a name="requirements"></a>
# Requirements

XACQ/XDCA depends on:
- [The Java Runtime Environment](https://www.java.com/en/download/)
- [Maven](https://maven.apache.org/) if you want to recompile XACQ/XDCA
- [Binsec](https://github.com/binsec/binsec) (>= 0.9.1) with Unisim\*
- Python 3 (to run the experiments)

\*We recommend installing Binsec through [opam](https://opam.ocaml.org/) by following these steps:
```shell
cd path/to/xacq
opam switch create . <OCAML_VERSION> # OCAML_VERSION < 5.0.0
opam pin ./binsecplugin/pathpredicate/   # pin the plugin package and install its dependencies (Binsec, Unisim ...)
```

To install the Python dependencies, run:
```shell
python3 -m venv path/to/venv
source path/to/venv/bin/activate
pip install -r requirements.txt
```

<a name="installation"></a>
# Installation

To use XACQ/XDCA, the `PRECA_PATH` environment variable must be set:
```shell
# You can put the following line in your .bashrc file (or equivalent file)
export PRECA_PATH=/path/to/xacq/directory
```

## Run from JAR

The `xacq.jar` file lets you use XACQ/XDCA without compiling it. See the [usage](#usage) section to find out how to use it.

## Compile from source

You can compile the code using Maven (the generated jar file is then in the `target` directory):
```shell
mvn clean compile assembly:single
cp target/preca-jar-with-dependencies.jar xacq.jar
```

<a name="usage"></a>
# Usage

You can list XACQ/XDCA's available options with:
```shell
java -jar xacq.jar -help
```

XACQ/XDCA takes the path to a configuration file as input:
```shell
java -jar xacq.jar -file <config>
```

The configuration file specifies which binary and which function are analyzed. You can get the documentation for the configuration file format with:
```shell
java -jar xacq.jar -helpconf
```

The explanation-related keys are:

| Key | Values | Default | Meaning |
|-----|--------|---------|---------|
| `algo` | `conacq`, `dca` | none (required) | acquisition algorithm |
| `explain` | `true`, `false` | `false` | use explanations (XACQ / XDCA) |
| `pos_explain` | `true`, `false` | `true` | use explanations on positive queries |
| `neg_explain` | `true`, `false` | `true` | use explanations on negative queries |

## Example

To check that your installation works correctly, you can run XACQ/XDCA on the provided strcat example.

For XACQ:
```shell
java -ea -jar xacq.jar -file ./examples/strcat_xacq.txt
```
For XDCA:
```shell
java -ea -jar xacq.jar -file ./examples/strcat_xdca.txt
```
(`strcat_conacq.txt` and `strcat_dca.txt` run CONACQ and DCA without explanations.)

In all cases, the output should end with:
```
*************Learned Network CL example ******
network var=4 cst=3
-------------------------
CONSTRAINTS:
Valid(var0)
Valid(var1)
NotOverlap(var0, var1)_or_StrlenEq0(var1)[0, 1, 2, 3]
-------------------------

*************Learned Network CL example (SMTLIB) ******
(and (valid v0) (valid v1) (or (not (overlap v0 v1)) (strleneq v1 #x00000000)))
```

<a name="experiments"></a>
# Experiments

We provide the needed datasets in the `datasets` directory and the script `scripts/bench.py` to replicate the results of our papers.
Help is available through:
```shell
python3 ./scripts/bench.py -h
```
Before launching the experiments, make sure to activate the Python environment:
```shell
source path/to/venv/bin/activate
```

Main `bench.py` options:

| Option | Meaning |
|--------|---------|
| `--algo conacq\|dca` | acquisition algorithm |
| `--explain` | enable explanations (XACQ / XDCA) |
| `--no_pos_explain` | disable explanations on positive queries (requires `--explain`) |
| `--no_neg_explain` | disable explanations on negative queries (requires `--explain`) |
| `--biaslvl max\|max2` | bias level max=level2 and max2= level3 |
| `--timeout <s>` | acquisition timeout in seconds |
| `--out <file>` | output JSON file |

After running your experiments, you can always recompute the statistics as follows:
```shell
python3 ./scripts/recompute_stats.py --file <json-file> --timeout <seconds>
```

<a name="ruleml"></a>
## RuleML+RR

To replicate the experiments from our RuleML+RR submission, run the following commands.

Level 1 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max --explain --bias_optim
```
Level 2 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max --explain --bias_optim
```
Level 3 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max2 --explain --bias_optim
```
Explanation quality:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max2 --explain
```

<a name="journal"></a>
## Constraints Journal

To replicate the experiments from the journal version, run the following commands.

### XACQ ablation study

XACQ+ (positive explanations only):
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max --explain --no_neg_explain --bias_optim
```
XACQ- (negative explanations only):
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo conacq --disj auto --biaslvl max --explain --no_pos_explain --bias_optim
```

### XDCA

Level 1 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo dca --disj auto --biaslvl max --explain
```
Level 2 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml --timeout 3600 --emulto 5 --out <out json> --algo dca --disj auto --biaslvl max --explain
```
Level 3 bases:
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml --timeout 3600 --emulto 5 --out <out json> --algo dca --disj auto --biaslvl max2 --explain
```

### XDCA ablation study

XDCA+ (positive explanations only):
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo dca --disj auto --biaslvl max --explain --no_neg_explain
```
XDCA- (negative explanations only):
```shell
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --algo dca --disj auto --biaslvl max --explain --no_pos_explain
```
