import os
import re
import sys

from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding, get_all_constants_of_CFM_mulitset, create_const_name
from cfmtoolbox_smt_encoder.cloningSMT import create_smt_cloning_encoding, get_all_constants_of_CFM_cloning, \
    create_amount_of_children_for_group_instance_cardinality_cloning, getMaxCardinality, \
    create_parent_list_for_feature_by_name, declare_cloned_constants
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
def encode_to_smt_cloning_base(cfm: CFM) -> str:
    encoding = ""
    encoding += create_smt_cloning_encoding(cfm, only_boolean_constants=True)

    return encoding

@app.command()
def encode_to_smt_cloning_with_child_int_constants(cfm: CFM) -> str:
    encoding = ""
    encoding += create_smt_cloning_encoding(cfm, only_boolean_constants=False)

    return encoding


@app.command()
def run_smtsolver_with_cloning_base(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(exit)"
    print(callSolverWithEncoding(encoding))


@app.command()
def run_smt_solver_with_cloning_base_minimize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    minimize_or_maximize_all_clones(cfm.root,encoding,False, cfm.root,[],True)

@app.command()
def run_smt_solver_with_cloning_base_maximize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    minimize_or_maximize_all_clones(cfm.root,encoding,True, cfm.root,[],True)

@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_minimize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    minimize_or_maximize_all_clones(cfm.root,encoding,False, cfm.root,[],False)

@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_maximize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    minimize_or_maximize_all_clones(cfm.root,encoding,True, cfm.root,[],False)

def minimize_or_maximize_all_clones(feature: Feature, encoding:str, maximize: bool,root: Feature, parent_list: list[int],only_boolean_constants: bool):

    def helper(depth, current_indices):
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            solver_cmd = encoding
            if maximize:
                solver_cmd += "(maximize"
            else:
                solver_cmd += "(minimize "
            solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning([feature], current_indices, only_boolean_constants)
            solver_cmd += ")"
            solver_cmd += "(check-sat)"
            solver_cmd += "(get-model)"
            solver_cmd += "(exit)"
            count_cardinality(callSolverWithEncoding(solver_cmd), feature, current_indices)
            return

        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return

    helper(0, [])

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        minimize_or_maximize_all_clones(feature, encoding, maximize, root, old_list, only_boolean_constants)



def count_cardinality(solver_output, feature, indices):
    count = 0
    constants = solver_output.split('-')

    for constant in constants:

        if len(indices) > 0:
            if ("Feature_" + feature.name + "_" + "_".join(map(str, indices))) in constant: # counts wrong -> for 1_1 it also counts 11_1 and 11_11 etc
                if "true" in constant:
                    count += 1
                match = re.search(r'Int\s*(\d+)', constant)
                if match:
                    count =  int(match.group(1))
        else:
            if ("Feature_" + feature.name ) in constant:
                if "true" in constant:
                    count += 1
                if "Int" in constant:
                    match = re.search(r'Int (\d+)', constant)
                    if match:
                        count =  int(match.group(1))

    if len(indices) > 0:
        print(feature.name + "_" + "_".join(map(str, indices)) + ": " + str(count))
    else:
        print(feature.name + "_" + "1" + ": " + str(count))




@app.command()
def run_smt_solver_with_cloning_base_gap_detection(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    find_gaps_in_all_clones(cfm.root,encoding,[],True)

@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_gap_detection(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    find_gaps_in_all_clones(cfm.root,encoding,[],False)


def find_gaps_in_all_clones(feature: Feature, encoding: str, parent_list: list[int], only_boolean_constants: bool):

    def helper(depth, current_indices):
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            for interval in feature.instance_cardinality.intervals:
                for j in range(interval.lower, interval.upper + 1):
                    solver_cmd = encoding
                    solver_cmd += "(assert (= "
                    solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning([feature], current_indices,only_boolean_constants=only_boolean_constants) + " "
                    solver_cmd += str(j) + "))"
                    solver_cmd += "(check-sat)"
                    solver_cmd += "(get-model)"
                    solver_cmd += "(exit)"
                    output = callSolverWithEncoding(solver_cmd)
                    if "unsat" in output:
                        print("Gap at: " + str(j) + " in Feature: " + feature.name + " ")
                    if "error" in output:
                        print(output)
            return

        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return

    helper(0, [])

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        find_gaps_in_all_clones(feature, encoding, old_list, only_boolean_constants)



def callSolverWithEncoding(encoding):
    path = os.path.join(os.path.abspath(sys.path[0]), "../../z3/z3/build/z3")
    cmd = [path, '-in', '-smt2']
    p = subprocess.run(cmd, stdout=subprocess.PIPE, input=encoding, encoding='ascii')
    return p.stdout