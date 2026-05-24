# XACQ : Precondition Constraint Acquisition Using Path Predicate

XACQ performs precondition inference relying on constraint acquisition and path predicates. XACQ does not need the source code of the function under analysis but only the binary.
XACQ is part of the BINSEC toolbox for binary-level program analysis and is build on top of the [constraint acquisition plateform](https://github.com/lirmm/ConstraintAcquisition).

# Table of Contents

1.  [Quick Setup - Docker Image](#docker_image)
2.  [Requirements](#requirements)
3.  [Installation](#installation)
4.  [Usage](#usage)
5.  [Experiments](#experiments)
    1. [Rule ML+RR](ruleml)

# Quick Setup - Docker Image

You do not need to clone this GitHub repository or download any source code to use XACQ. As long as you have Docker installed, you can run the tool directly from your terminal. Docker will automatically download the image from the registry the first time you execute it.
```shell
sudo docker pull sdjebour/xacq:latest
sudo docker run --rm -it --user opam sdjebour/xacq:latest
```
When entering the Docker container, you must initialize the OCaml environment by running:
```
eval $(opam env)
```
All set! You can now proceed to the Usage and Experiments sections below.

# Requirements

The XACQ framework depends on:
- [The Java Runtime Environment](https://www.java.com/en/download/)
- [Maven](https://maven.apache.org/) if you want to recompile PreCA
- [Binsec](https://github.com/binsec/binsec) (>= 0.9.1) with Unisim\*
- Python 3 (to run the experiments)


\*We recommend to install Binsec through [opam](https://opam.ocaml.org/), by following these steps: 
```shell
cd path/to/xacq
opam switch create . <OCAML_VERSION> # OCAML_VERSION < 5.0.0
opam pin ./binsecplugin/concrete/   # pin the libconcrete package and install its dependencies (Binsec, Unisim ...)
```

To install the python dependencies, run:
```
python3 -m venv path/to/venv
source path/to/venv/bin/activate
pip install -r requirements.txt
```

# Installation

To use XACQ the `PRECA_PATH` environment variable should be set:
```shell
# You can put the following line in your .bashrc file (or equivalent file)
export PRECA_PATH=/path/to/xacq/directory   
```

## Run from JAR

The `xacq.jar` file is available to use XACQ without compiling it. See the [usage](#usage) section to found out how to use it.

## Compile from source

You can compile the code using maven (the generated jar file is then in the `target` directory):
```shell
mvn clean compile assembly:single
cp target/<jarfile> xacq.jar
```

# Usage

You can get XACQ's available options:
```shell
java -jar xacq.jar -help
```

XACQ takes as input the path to the configuration file as follows:
```shell
java -jar xacq.jar -file <config>
```

Such a configuration file enables to specify which binary and which function is analyzed. You can get the documentation for the configuration file format with:
```shell
java -jar xacq.jar -helpconf
```

## Example

To check that your install works correctly, you can run XACQ over the given strcat example:
```shell
java -ea -jar xacq.jar -file ./examples/strcat_econacq.txt
```

The output should end with:
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

# Experiments

We provide the needed datasets in the `datasets` directory and the script `scripts/bench.py` to replicate the results in the submission. 
The help is available through
```shell
python3 ./scripts/bench.py -h
```
To launch the experiments, make sure to activate the Python environment first:
```
source venv/bin/activate
```

Moreover, after running your experiments, you can always recompute the statistics as follows:
```shell
python3 ./scripts/recompute_stats.py --file <json-file> --timeout <seconds>
```

## Rule ML+RR

To replicate experiments from our submission run the following commands:
For Level 1 Bases :
```
python3 ./scripts/bench.py --dataset ./datasets/configs/ruleml_min --timeout 3600 --emulto 5 --out <out json> --disj auto --biaslvl max --explain --bias_optim
```
For Level 2 Bases :
```
python3 ./scripts/bench.py --dataset ./datasets/ruleml --timeout 3600 --emulto 5 --out <out json> --disj auto --biaslvl max --explain --bias_optim
```
For Level 3 Bases :
```
python3 ./scripts/bench.py --dataset ./datasets/ruleml --timeout 3600 --emulto 5 --out <out json> --disj auto --biaslvl max2 --explain --bias_optim
```
To have the informations concerning qualities of explanations:
```
python3 ./scripts/bench.py --dataset ./datasets/ruleml --timeout 3600 --emulto 5 --out <out json> --disj auto --biaslvl max2 --explain
```



