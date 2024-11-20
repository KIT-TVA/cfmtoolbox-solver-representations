import os
import sys
from pyexpat import features

from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding, get_all_constants_of_CFM_mulitset, create_const_name
from cfmtoolbox_smt_encoder.cloningSMT import create_smt_cloning_encoding, get_all_constants_of_CFM_cloning, \
    create_amount_of_children_for_group_instance_cardinality_cloning, getMaxCardinality
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
    encoding = ""
    encoding += create_smt_cloning_encoding(cfm)

    return encoding


@app.command()
def run_smtsolver_with_cloning(cfm: CFM):
    encoding = encode_to_smt_cloning(cfm)
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(exit)"
    print(callSolverWithEncoding(encoding))


@app.command()
def run_smt_solver_with_cloning_minimize_cardinalities(cfm: CFM):
    features = cfm.root.children
    encoding = create_smt_cloning_encoding(cfm)
    minimize_or_maximize_all_clones(features,encoding,False)

@app.command()
def run_smt_solver_with_cloning_maximize_cardinalities(cfm: CFM):
    features = cfm.root.children
    encoding = create_smt_cloning_encoding(cfm)
    minimize_or_maximize_all_clones(features,encoding,True)

def minimize_or_maximize_all_clones(features: list[Feature], encoding:str, maximize: bool):
    for feature in features:
        for i in range(1,getMaxCardinality(feature.parent.instance_cardinality.intervals)+1):
            solver_cmd = encoding
            if maximize:
                solver_cmd += "(maximize"
            else:
                solver_cmd += "(minimize "
            solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning([feature],i)
            solver_cmd += ")"
            solver_cmd += "(check-sat)"
            solver_cmd += "(get-model)"
            solver_cmd += "(exit)"
            count_cardinality(callSolverWithEncoding(solver_cmd),feature,i)

            minimize_or_maximize_all_clones(feature.children,encoding,maximize)



def count_cardinality(solver_output, feature, parent_number):
    count = 0
    constants = solver_output.split('-')
    for constant in constants:
        if ("Feature_" + feature.name + "_" + str(parent_number)) in constant:
            if "true" in constant:
                count += 1


    print(feature.name + "_" + str(parent_number) + ": " + str(count))




@app.command()
def run_smt_solver_with_cloning_gap_detection(cfm: CFM):
    features = cfm.root.children
    encoding = create_smt_cloning_encoding(cfm)
    find_gaps_in_all_clones(features,encoding)



def find_gaps_in_all_clones(features: list[Feature], encoding: str):
    for feature in features:
        for i in range(1, getMaxCardinality(feature.parent.instance_cardinality.intervals) + 1):
            for interval in feature.instance_cardinality.intervals:
                for j in range(interval.lower, interval.upper + 1):
                    solver_cmd = encoding
                    solver_cmd += "(assert (= "
                    solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning([feature], i) + " "
                    solver_cmd +=  str(j) + "))"
                    #print(create_amount_of_children_for_group_instance_cardinality_cloning([feature],i))
                    #solver_cmd += ")"
                    solver_cmd += "(check-sat)"
                    solver_cmd += "(get-model)"
                    solver_cmd += "(exit)"
                    output = callSolverWithEncoding(solver_cmd)
                    #print(solver_cmd)
                    #print(output)
                    if "unsat" in output:
                        print("Gap at: " + str(j) + " in Feature: " + feature.name + " ")
                    if "error" in output:
                        print(output)

            find_gaps_in_all_clones(feature.children, encoding)


def callSolverWithEncoding(encoding):
    path = os.path.join(os.path.abspath(sys.path[0]), "../../z3/z3/build/z3")
    cmd = [path, '-in', '-smt2']
    p = subprocess.run(cmd, stdout=subprocess.PIPE, input=encoding, encoding='ascii')
    return p.stdout