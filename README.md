# CFMToolbox-Solver-Representation

## Installation
To use the Plugins with the CFM Toolbox it first needs to be build via poetry.
Therefore got to one of the three directories (CSP, ILP or SMT) and run the following command.

```
poetry build
```

Then install the plugin, which should install the dependency  [CFMtoolbox](https://github.com/KIT-TVA/cfmtoolbox) and for CSP and ILP install [Or-Tools](https://developers.google.com/optimization/install/python) as well.

```
pip3 install Path-To-The-Plugin/cfmtoolbox-smt-encoder/dist/cfmtoolbox_smt_encoder-0.1.0.tar.gz
```

For the SMT Plugin an additional Installation of Z3 is necessary (see [here](https://github.com/Z3Prover/z3)).
And the path to the solver should then be added to the init.py of the SMT Encoding Plugin.


## Run 

The Plugin adds the following commands to the toolbox.

See [CSP](/CSP/README.md), [SMT](/SMT/README.md) and [ILP](/ILP/README.md)


