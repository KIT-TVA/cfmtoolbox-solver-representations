from cfmtoolbox import CFM, Feature, Interval
from cfmtoolbox.plugins.big_m import get_global_upper_bound

from cfmtoolbox_csp_encoder.multisetCSP import create_const_name, \
    create_assert_feature_instance_cardinality, create_assert_group_instance_cardinality
from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import CpModel

big_m = 0
variables = {}




def create_ilp_cloning_encoding(cfm: CFM,only_boolean_constants: bool):
    """
    :param cfm: An instance of the CFM object which represents a cardinality-based feature model.
                This model is used as the basis for creating the ILP encoding.
    :param only_boolean_constants: A boolean flag indicating whether to only create boolean constant
                for every feature instance or int constants for the leave features.This can
                reduce the overhead of the encoding
    :return: A string that represents the SMT encoding of the provided CFM.
    """

    global big_m
    big_m = get_global_upper_bound(cfm.root)
    print(big_m)
    model = cp_model.CpModel()
    print("Encoding CFM...")
    declare_cloned_constants(model, cfm.root,[],
                                         only_boolean_constants=only_boolean_constants)
    create_assert_feature_instance_cardinality_cloning_csp(model, cfm.root,[],
                                                           only_boolean_constants=only_boolean_constants)

    create_assert_group_instance_cardinality_cloning_csp(model, cfm.root,[],only_boolean_constants=only_boolean_constants)



    print("Encoding complete.")

    return model



def declare_cloned_constants(model: CpModel, parent: Feature, parent_list: list[int],
                             only_boolean_constants: bool):
    max = getMaxCardinality(parent.instance_cardinality.intervals)

    if parent.parent is None:
        for j in range(1, max + 1):
            variables[create_const_name(parent)] = model.new_bool_var(create_const_name(parent))

    else:
        # if it is a leave then do not append the instance cardinality, because the last constant will be an integer
        if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):
            parent_list.append(max)
        # Define the recursive function that generates n nested loops
        def helper(depth, current_indices):
            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):
                # decides whether only the constants names are created or the declarations for the encoding
                    # when it is a leave and not the base cloning approach then add Int datatype, else Bool
                    if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):
                        variables[create_const_name(parent)] = model.new_bool_var(
                            create_const_name(parent))
                    else:
                        variables[create_const_name(parent)] = model.new_bool_var(create_const_name(parent))


            loop_code = ""
            # Loop through the range based on the current depth value in arr[depth]
            for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                current_indices.append(i)  # Add the current index to the list
                loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
                current_indices.pop()
            return loop_code

        helper(0, [])


    for feature in parent.children:
        old_list = parent_list.copy()
        declare_cloned_constants(model, feature, old_list,only_boolean_constants)



def create_assert_feature_instance_cardinality_cloning_csp(model, feature,parent_list: list[
    int], only_boolean_constants):
    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):

        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):

            interval_literals = []

            for i, interval in enumerate(feature.instance_cardinality.intervals):
                interval_literal = model.new_bool_var(
                    "interval_literal_" + str(i) + "_" + feature.name)
                interval_literals.append(interval_literal)
                sum_variable = create_sum_of_feature_instance(model, feature, current_indices,
                                                              only_boolean_constants)
                if feature.parent is not None:

                    if len(current_indices) > 0:
                        parent_variable = variables[create_const_name(feature.parent) + "_" + "_".join(
                            map(str, current_indices)) + " " + str(interval.upper)]
                    else:
                        parent_variable = variables[create_const_name(
                            feature.parent) + "_" + "1" + " " + str(interval.upper)]

                    model.add(sum_variable >=
                              interval.lower * parent_variable).only_enforce_if(
                        interval_literal)
                    model.add(
                        sum_variable <= interval.upper * parent_variable).only_enforce_if(
                        interval_literal)
                else:
                    model.add(
                        sum_variable >= interval.lower).only_enforce_if(interval_literal)
                    model.add(
                        sum_variable <= interval.upper).only_enforce_if(interval_literal)
            model.add_bool_xor(interval_literals)

        loop_code = ""
        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[
                              depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return loop_code

    helper(0, [])

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        create_assert_feature_instance_cardinality_cloning_csp(model, feature, old_list,
                                                                              only_boolean_constants)


def create_sum_of_feature_instance(model: CpModel ,feature: Feature, indices,
                                   only_boolean_constants:
bool):
    upper_bound = big_m * len(feature.children)
    sum_variables = []
    if only_boolean_constants or (not only_boolean_constants and len(feature.children) >= 1):
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):

            if len(indices) > 0:
                sum_variables.append(variables[create_const_name(feature) + "_" + "_".join(map(str, indices)) + "_" + str(i)])
            else:
                sum_variables.append(variables[create_const_name(feature) +  "_" +
                                                     str(i)])

    else:
       sum_variables.append(variables[create_const_name(feature) + "_" + "_".join(map(str, indices))])

    total_sum_variables = model.new_int_var(0, upper_bound, "total_sum_variables_" + str(
            feature.name))
    model.add(total_sum_variables == sum(sum_variables))


    return total_sum_variables



def create_assert_group_instance_cardinality_cloning_csp(model: CpModel, feature: Feature, parent_list: list[int],
                                                         only_boolean_constants: bool):



def getMaxCardinality(intervals: list[Interval]) -> int:
    max = 1
    for interval in intervals:
        if interval.upper >= max:
            max = interval.upper

    return max
