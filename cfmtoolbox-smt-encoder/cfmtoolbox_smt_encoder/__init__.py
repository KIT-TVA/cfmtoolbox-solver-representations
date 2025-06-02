import os
import re
import sys
from cfmtoolbox import app, CFM, Feature
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding, create_const_name
from cfmtoolbox_smt_encoder.cloningSMT import create_smt_cloning_encoding, \
    create_amount_of_children_for_group_instance_cardinality_cloning, getMaxCardinality, \
    get_min_cardinality, add_constraint_to_remove_permutations
import subprocess



@app.command()
def encode_to_smt_multiset(cfm: CFM) -> str:
    """
    :param cfm: The input Cardinality-based Feature Model that needs to be encoded into SMT multiset format
    :return: A string representing the SMT multiset encoding of the input CFM object
    """
    encoding = create_smt_multiset_encoding(cfm,sampling=True)
    return encoding

@app.command()
def get_smt_multiset_stats(cfm: CFM):
    encoding = create_smt_multiset_encoding(cfm,sampling=False)
    #print_encoding_stats(encoding)

@app.command()
def get_smt_cloning_basis_stats(cfm: CFM):
    encoding = create_smt_cloning_encoding(cfm,only_boolean_constants=True)
    #print_encoding_stats(encoding)

@app.command()
def get_smt_cloning_integer_leaves_stats(cfm: CFM):
    encoding = create_smt_cloning_encoding(cfm,only_boolean_constants=False)
    #print_encoding_stats(encoding)

def print_encoding_stats(encoding):
   ## print(encoding)

    encoding += "(set-option :stats true)"
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(get-info :all-statistics)"
    encoding += "(get-info :assertion-stack-size)"
    encoding += "(get-info :decls)"
    
    output = callSolverWithEncoding(encoding)
    print(output)



@app.command()
def run_smtsolver_with_multisetencoding(cfm: CFM):
    """
    :param cfm: The input Cardinality-based Feature Model that needs to be encoded into SMT multiset format
    :return: None. The function prints the result of the SMT solver.
    """
    encoding = create_smt_multiset_encoding(cfm,sampling=True)
    encoding += "(check-sat)"
    encoding += "(get-model)"
    encoding += "(exit)"
    print(callSolverWithEncoding(encoding))

@app.command()
def run_smtsolver_with_multiset_bound_analysis(cfm: CFM):
    encoding = create_smt_multiset_encoding(cfm, sampling=False)
    find_actual_max(encoding, cfm.root, 1)
    find_actual_min(encoding, cfm.root, 1)

@app.command()
def run_smt_solver_with_multisetencoding_maximize_cardinalities(cfm: CFM):
    """
    :param cfm: The input Cardinality-based Feature Model, which gets encoded, and all Feature Cardinalities are maximized by the solver
    :return: Prints the result of the SMT solver for each constant(Feature cardinality) after encoding and maximization procedures.
    """
    encoding = create_smt_multiset_encoding(cfm,sampling=False)
    find_actual_max(encoding, cfm.root,1)

def find_actual_max(encoding, feature:Feature, max_parent_cardinality: int):
    solver_cmd = encoding
    solver_cmd += "(maximize "
    solver_cmd += create_const_name(feature)
    solver_cmd += ")"
    solver_cmd += "(check-sat)"
    solver_cmd += "(get-value (" + create_const_name(feature) + "))"
    solver_cmd += "(exit)"
    result = callSolverWithEncoding(solver_cmd)
    match = re.search('\(\((\w+_\w+)\s(\d+)\)\)', result)
    if  not "unsat" in result:

        if int(match.__getitem__(2)) > 1:
            actual_max = int(match.__getitem__(2)) / max_parent_cardinality
            new_max = round(max_parent_cardinality * actual_max, None)
        else:
            actual_max = int(match.__getitem__(2))
            new_max = max_parent_cardinality
        if actual_max < getMaxCardinality(feature.instance_cardinality.intervals):
            print(match.__getitem__(1) + ": ")
            print("Given feature instance cardinality: " + str(getMaxCardinality(
                feature.instance_cardinality.intervals)) + "\n")
            print("Actual Max Feature Instance Cardinality " + str(round(actual_max, None)) + "\n")
    else:
        print("unsat: " + create_const_name(feature) + "" + "\n")
        new_max = max_parent_cardinality

    for child in feature.children:
        find_actual_max(encoding, child, new_max)



@app.command()
def run_smt_solver_with_multisetencoding_minimize_cardinalities(cfm: CFM):
    """
    :param cfm: The input Cardinality-based Feature Model, which gets encoded, and all Feature Cardinalities are minimized by the solver
    :return: Prints the result of the SMT solver for each constant(Feature cardinality) after encoding and minimized procedures.
    """
    encoding = create_smt_multiset_encoding(cfm,sampling=False)
    find_actual_min(encoding, cfm.root, 1)


def find_actual_min(encoding, feature:Feature, min_parent_cardinality: int):
    solver_cmd = encoding
    solver_cmd += "(minimize "
    solver_cmd += create_const_name(feature)
    solver_cmd += ")"
    solver_cmd += "(check-sat)"
    solver_cmd += "(get-value (" + create_const_name(feature) + "))"
    solver_cmd += "(exit)"
    result = callSolverWithEncoding(solver_cmd)
    match = re.search('\(\((\w+_\w+)\s(\d+)\)\)', result)
    print(feature.name + " " +  str(min_parent_cardinality) + " " + str(int(match.__getitem__(
        2))) + "\n")
    if int(match.__getitem__(2)) > 1 and min_parent_cardinality >= 1:

        actual_min = int(match.__getitem__(2)) / min_parent_cardinality
        min_parent_cardinality = round(min_parent_cardinality * actual_min, None)

    else:
        actual_min = int(match.__getitem__(2))
    if actual_min > get_min_cardinality(feature.instance_cardinality.intervals):
        print(match.__getitem__(1) + ": ")
        print("Given feature instance cardinality: " + str(get_min_cardinality(
            feature.instance_cardinality.intervals)) + "\n")
        print("Actual Min Feature Instance Cardinality " + str(actual_min) + "\n")


    for child in feature.children:
        find_actual_min(encoding, child, min_parent_cardinality)



@app.command()
def run_smt_solver_with_multisetencoding_gap_detection(cfm: CFM):
    """
    :param cfm: The input Cardinality-based Feature Model, which gets encoded
    :return: Prints the result of the SMT solver for each constant asserted to their possible cardinalities.
    """
    list_features = cfm.features
    encoding = create_smt_multiset_encoding(cfm,sampling=False)
    print("Searching for Gaps...")
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
    """
    :param cfm: The input Cardinality-based Feature Model that needs to be encoded into SMT cloning basic format
    :return:The function returns the encoding of the CFM in the basis variant of SMT cloning approach.
        The base cloning approach creates boolean constants for every possible Feature Instance Cardinality.
    """
    encoding = ""
    encoding += create_smt_cloning_encoding(cfm, only_boolean_constants=True)

    return encoding

@app.command()
def encode_to_smt_cloning_with_child_int_constants(cfm: CFM) -> str:
    """
   :param cfm: The input Cardinality-based Feature Model that needs to be encoded into SMT cloning format where the leaves are integers constants
   :return:The function returns the encoding of the CFM in the cloning format where the leaves are integers constants.
       This cloning approach creates boolean constants for every Feature, possible Feature Instance Cardinality, which are not leaves. The leaves create int constants
   """
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
    return minimize_or_maximize_all_clones(cfm.root,encoding,False, cfm.root,[],True)

@app.command()
def run_smt_solver_with_cloning_base_maximize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    return minimize_or_maximize_all_clones(cfm.root,encoding,True, cfm.root,[],True)

@app.command()
def run_smtsolver_with_cloning_with_child_int_constants_bound_analysis(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    minimize_or_maximize_all_clones(cfm.root,encoding,False, cfm.root,[],False)
    minimize_or_maximize_all_clones(cfm.root, encoding, True, cfm.root, [], False)


@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_minimize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    return minimize_or_maximize_all_clones(cfm.root,encoding,False, cfm.root,[],False)

@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_maximize_cardinalities(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    return minimize_or_maximize_all_clones(cfm.root,encoding,True, cfm.root,[],False)

def minimize_or_maximize_all_clones(feature: Feature, encoding:str, maximize: bool,root: Feature, parent_list: list[int],only_boolean_constants: bool):
    max_cardinalities = ""


    solver_cmd = encoding
    if maximize:
        solver_cmd += "(maximize"
    else:
        solver_cmd += "(minimize "
    solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning(
        [feature], parent_list, only_boolean_constants)
    solver_cmd += ")"
    solver_cmd += "(check-sat)"
    solver_cmd += "(get-model)"
    solver_cmd += "(exit)"
    max_cardinalities += count_cardinality(callSolverWithEncoding(solver_cmd), feature,
                                         parent_list) + " "

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        max_cardinalities += minimize_or_maximize_all_clones(feature, encoding, maximize, root, old_list,
                                        only_boolean_constants)
    return max_cardinalities






def count_cardinality(solver_output, feature, indices):
    count = 0
    constants = solver_output.split('-')

    print(feature.name)

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
        max_cardinality = feature.name + "_" + "_".join(map(str, indices)) + ": " + str(count)
        if count  < getMaxCardinality(feature.instance_cardinality.intervals):
            print(max_cardinality)
        return max_cardinality
    else:
        max_cardinality = feature.name + "_" + "1" + ": " + str(count)
        if count < getMaxCardinality(feature.instance_cardinality.intervals):
            print(max_cardinality + " instead of " + str(getMaxCardinality(
                feature.instance_cardinality.intervals)))
        return max_cardinality




@app.command()
def run_smt_solver_with_cloning_base_gap_detection(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)
    print("Searching for Gaps...")
    return find_gaps_in_all_clones(cfm.root,encoding,[],True)

@app.command()
def run_smt_solver_with_cloning_with_child_int_constants_gap_detection(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    print("Searching for Gaps...")
    return find_gaps_in_all_clones(cfm.root,encoding,[],False)


def find_gaps_in_all_clones(feature: Feature, encoding: str, parent_list: list[int], only_boolean_constants: bool):
    gaps = ""

    print(feature.name)
    for interval in feature.instance_cardinality.intervals:
        for j in range(interval.lower, interval.upper + 1):
            solver_cmd = encoding
            solver_cmd += "(assert (= "
            solver_cmd += create_amount_of_children_for_group_instance_cardinality_cloning(
                [feature], parent_list, only_boolean_constants=only_boolean_constants) + " "
            solver_cmd += str(j) + "))"
            solver_cmd += "(check-sat)"
            solver_cmd += "(get-model)"
            solver_cmd += "(exit)"
            output = callSolverWithEncoding(solver_cmd)
            if "unsat" in output:
                gap = "Gap at: " + str(j) + " in Feature: " + feature.name + " "
                print(gap)
                gaps += gap
            if ("error" in output) and not("unsat" in output) and not("sat" in output):
                print("error")
                #print(output)

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        #max_cardinality = max_cardinality if (max_cardinality != 0) else 1
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        gaps += find_gaps_in_all_clones(feature, encoding, old_list, only_boolean_constants)
    return gaps


@app.command()
def run_smt_cloning_basis_sampling(cfm: CFM):
    encoding = encode_to_smt_cloning_base(cfm)

    amount_samples = count_samples(encoding)
    print(amount_samples)




@app.command()
def run_smt_cloning_with_integer_leaves_sampling(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)

    amount_samples = count_samples(encoding)
    print(amount_samples)

@app.command()
def run_smt_cloning_with_integer_leaves_sampling_without_permutation(cfm: CFM):
    encoding = encode_to_smt_cloning_with_child_int_constants(cfm)
    encoding += add_constraint_to_remove_permutations(cfm.root,[],False)
    print(encoding)
    amount_samples = count_samples(encoding)
    print(amount_samples)


@app.command()
def run_smt_multiset_with_cloning_sampling(cfm: CFM):
    encoding = encode_to_smt_multiset(cfm)

    amount_samples = count_samples(encoding)
    print(amount_samples)



def count_samples(encoding):
    count = 0
    new_encoding = encoding
    new_encoding += "(check-sat)"
    new_encoding += "(get-model)"
    new_encoding += "(exit)"
    output = callSolverWithEncoding(new_encoding)
    while ("unsat" or "error") not in output:
        encoding += "(assert (not (and"
        constants = output.split('-')
        for constant in constants:
            if "Feature" in constant:
                feature_value_split = constant.split(" ")
                value = feature_value_split[7].split(")")
                encoding += "(= " + feature_value_split[1] + " " + value[0] + ")"
                #print("(= " + feature_value_split[1] + " " + value[0] + ")\n")
        encoding += ")))"
        new_encoding = encoding
        new_encoding += "(check-sat)"
        new_encoding += "(get-model)"
        new_encoding += "(exit)"
        output = callSolverWithEncoding(new_encoding)
        count = count + 1
        print(count)
    return count


def callSolverWithEncoding(encoding):
    """
    :param encoding: A string representing the SMT2 encoding to be passed to the solver.
    :return: The standard output from the solver as a string.
    """
    path = os.path.join(os.path.abspath(sys.path[0]), "../../z3/z3/build/z3") # needs #
    # test ../../../../../z3/z3/build/z3
    # to be
    # moved to env variable
    cmd = [path, '-in', '-smt2']
    p = subprocess.run(cmd, stdout=subprocess.PIPE, input=encoding, encoding='ascii')
    return p.stdout