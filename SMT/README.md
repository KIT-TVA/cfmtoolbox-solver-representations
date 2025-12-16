# CFMToolboxPluginSMTEncoding

## Installation
To use the Plugin with the CFM Toolbox it first needs to be build via poetry.
Therefore got to the directory where the repo is saved and run the following command.

```
poetry build
```

Then install the Plugin and the CFM Toolbox via the following commands.

CFMToolbox
```
pip3 install cfmtoolbox
```

Install the plugin
```
pip3 install Path-To-The-Plugin/cfmtoolbox-smt-encoder/dist/cfmtoolbox_smt_encoder-0.1.0.tar.gz
```


## Run 

The Plugin adds the following commands to the toolbox.

### SMT Multiset Encoding Variant
 

Searches for Gaps in the CFM with the multiset approach encoding.
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM  run-smt-solver-with-multiset-gap-detection
```

Return the maximum feature instance cardinality for every feature. This methode uses the multiset encoding. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM  run-smt-solver-with-multiset-maximize-cardinalities
```
Return the minimum feature instance cardinality for every feature. This methode uses the multiset encoding. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM  run-smt-solver-with-multiset-minimize-cardinalities
```


### SMT Cloning Basic Variant

Searches for Gaps in the CFM with the basic cloning approach encoding.
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM  run-smt-solver-with-cloning-base-gap-detection
```

Return the maximum feature instance cardinality for every feature. This methode uses the basic cloning encoding. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM   run-smt-solver-with-cloning-base-maximize-cardinalities
```
Return the minimum feature instance cardinality for every feature. This methode uses the basic cloning encoding. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM   run-smt-solver-with-cloning-base-minimize-cardinalities
```

### SMT Cloning with Integer Leaves

Searches for Gaps in the CFM with the cloning approach encoding, where the leave nodes are represented as int constants.
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM  run-smt-solver-with-cloning-with-child-int-constants-gap-detection
```

Return the maximum feature instance cardinality for every feature. This methode uses the cloning encoding with integer leaves. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM   run-smt-solver-with-cloning-with-child-int-constants-maximize-cardinalities
```
Return the minimum feature instance cardinality for every feature. This methode uses the cloning encoding with integer leaves. 
```
python3 -m cfmtoolbox --import Path-TO-JSON-OF-CFM   run-smt-solver-with-cloning-with-child-int-constants-minimize-cardinalities
```
