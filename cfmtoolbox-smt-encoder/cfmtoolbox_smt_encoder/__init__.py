import os
import sys

from cfmtoolbox import app, CFM
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding, get_all_constants_of_CFM_mulitset, create_const_name
from cfmtoolbox_smt_encoder.cloningSMT import create_smt_cloning_encoding
import subprocess




@app.command()
def encode_to_smt_multiset(cfm: CFM) -> str:
    encoding = create_smt_multiset_encoding(cfm)
    return encoding

@app.command()
def run_smtsolver_with_multisetencoding(cfm: CFM):
    encoding = create_smt_multiset_encoding(cfm)
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(exit)"
    print(callSolverWithEncoding(encoding))
    #p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True)
    #out = p.communicate(input=encoding)
    #result = out.split('\n')
    #for lin in result:
    #    print(lin)

@app.command()
def run_smt_solver_with_multisetencoding_maximize_cardinalities(cfm: CFM):
    list_constants = get_all_constants_of_CFM_mulitset(cfm)
    encoding = create_smt_multiset_encoding(cfm)
    print(len(list_constants))
    for constant in list_constants:
        solver_cmd = encoding
        solver_cmd += "(maximize "
        solver_cmd += constant
        solver_cmd += ")"
        solver_cmd += "(check-sat)"
        solver_cmd += "(get-value (" + constant + "))"
        solver_cmd += "(exit)"
        print(callSolverWithEncoding(solver_cmd))


@app.command()
def run_smt_solver_with_multisetencoding_minimize_cardinalities(cfm: CFM):
    list_constants = get_all_constants_of_CFM_mulitset(cfm)
    encoding = create_smt_multiset_encoding(cfm)
    print(len(list_constants))
    for constant in list_constants:
        solver_cmd = encoding
        solver_cmd += "(minimize "
        solver_cmd += constant
        solver_cmd += ")"
        solver_cmd += "(check-sat)"
        solver_cmd += "(get-value (" + constant + "))"
        solver_cmd += "(exit)"
        print(callSolverWithEncoding(solver_cmd))


@app.command()
def run_smt_solver_with_multisetencoding_gap_detection(cfm: CFM):
    list_features = cfm.features
    encoding = create_smt_multiset_encoding(cfm)
    for feature in list_features:
        for interval in feature.instance_cardinality.intervals:
            for cardinality in range(interval.lower, interval.upper + 1):
                solver_cmd = encoding
                solver_cmd += "(assert (= "
                solver_cmd += create_const_name(feature) + " "
                solver_cmd += str(cardinality)
                solver_cmd += "))"
                solver_cmd += "(check-sat)"
                solver_cmd += "(exit)"
                output = callSolverWithEncoding(solver_cmd)
                if output.__contains__("unsat"):
                    print("Gap at: " + str(cardinality) + " in Feature: " + str(feature.name))


@app.command()
def encode_to_smt_cloning(cfm: CFM) -> str:
    print("Encoding CFM...")
    encoding = ""
    encoding += create_smt_cloning_encoding(cfm)


    print(encoding)
    return encoding


def callSolverWithEncoding(encoding):
    path = os.path.join(os.path.abspath(sys.path[0]), "../../z3/z3/build/z3")
    cmd = [path, '-in', '-smt2']
    p = subprocess.run(cmd, stdout=subprocess.PIPE, input=encoding, encoding='ascii')
    return p.stdout