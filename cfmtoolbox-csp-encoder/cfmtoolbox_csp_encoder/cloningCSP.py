from cfmtoolbox import CFM, Feature, Interval
from cfmtoolbox.plugins.big_m import get_global_upper_bound

from cfmtoolbox_csp_encoder.multisetCSP import create_const_name, \
    create_assert_feature_instance_cardinality, create_assert_group_instance_cardinality
from cfmtoolbox_smt_encoder.mulitsetSMT import create_amount_of_children_for_group_type_cardinality
from ortools.sat.python import cp_model
from ortools.sat.python.cp_model import CpModel

big_m = 0
variables = {}




def create_csp_cloning_encoding(cfm: CFM,only_boolean_constants: bool):
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
    declare_cloned_constants_csp(model, cfm.root,[],
                                         only_boolean_constants=only_boolean_constants)
    create_assert_feature_instance_cardinality_cloning_csp(model, cfm.root,[],
                                                         only_boolean_constants=only_boolean_constants)

    create_assert_group_cardinality_cloning_csp(model,True, cfm.root,[],
                                                      only_boolean_constants=only_boolean_constants)

    create_assert_group_cardinality_cloning_csp(model,False, cfm.root,[],
                                                only_boolean_constants=only_boolean_constants)



    print("Encoding complete.")

    return model



def declare_cloned_constants_csp(model: CpModel, parent: Feature, parent_list: list[int],
                             only_boolean_constants: bool):
    max = getMaxCardinality(parent.instance_cardinality.intervals)

    if parent.parent is None:
        for j in range(1, max + 1):
            name = create_const_name(parent) + "_" + str(j)
            variables[name] = model.new_bool_var(name)

    else:
        # if it is a leave then do not append the instance cardinality, because the last constant will be an integer
        if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):
            parent_list.append(max)


        # Define the recursive function that generates n nested loops
        def helper(depth, current_indices):
            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):
                variable_name = create_const_name(parent) + "_" + "_".join(map(str,
                                                                               current_indices))
                # when it is a leave and not the base cloning approach then add Int datatype, else Bool
                if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):

                    variables[variable_name] = model.new_bool_var(variable_name)
                else:
                    variables[variable_name] = model.new_int_var(
                                                        0,big_m,variable_name)
                return
            # Loop through the range based on the current depth value in arr[depth]
            for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                current_indices.append(i)  # Add the current index to the list
                helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
                current_indices.pop()

        helper(0, [])


    for feature in parent.children:
        old_list = parent_list.copy()
        declare_cloned_constants_csp(model, feature, old_list,only_boolean_constants)




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
                sum_variables = create_sum_of_feature_instance(feature, current_indices,
                                                              only_boolean_constants)
                if feature.parent is not None:
                    if len(current_indices) > 0:
                        parent_variable = variables[create_const_name(feature.parent) + "_" + "_".join(
                            map(str, current_indices))]
                    else:
                        parent_variable = variables[create_const_name(
                            feature.parent) + "_" + "1"]

                    model.add(sum(sum_variables) >=
                              interval.lower * parent_variable).only_enforce_if(
                        interval_literal)
                    model.add(
                        sum(sum_variables) <= interval.upper * parent_variable).only_enforce_if(
                        interval_literal)
                else:
                    model.add(
                        sum(sum_variables) >= interval.lower).only_enforce_if(interval_literal)
                    model.add(
                        sum(sum_variables) <= interval.upper).only_enforce_if(interval_literal)
            model.add_bool_xor(interval_literals)
            return

        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[
                              depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()


    helper(0, [])

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        create_assert_feature_instance_cardinality_cloning_csp(model, feature, old_list,
                                                                              only_boolean_constants)


def create_sum_of_feature_instance(feature: Feature, indices,
                                   only_boolean_constants:bool):
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


    return sum_variables



def create_assert_group_cardinality_cloning_csp(model: CpModel,instance: bool, feature: Feature,
                                                parent_list: list[int], only_boolean_constants: bool):

    if len(feature.children) != 0:
        if feature.parent is not None:
            max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
            parent_list.append(max_cardinality)

        # Define the recursive function that generates n nested loops
        def helper(depth, current_indices):

            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):

                if instance:
                    interval = feature.group_instance_cardinality.intervals.__getitem__(0)
                    sum_variables = create_amount_of_children_for_group_instance_cardinality_cloning_csp(
                        feature.children, current_indices, only_boolean_constants)
                else:
                    interval = feature.group_type_cardinality.intervals.__getitem__(0)
                    sum_variables = create_amount_of_children_for_group_type_cardinality_cloning_csp(
                        model, feature.children, current_indices, only_boolean_constants)

                if feature.parent is not None:

                    if len(current_indices) > 0:
                        parent_variable = variables[create_const_name(feature) + "_" + "_".join(
                            map(str, current_indices))]
                    else:
                        parent_variable = variables[create_const_name(
                            feature.parent) + "_" + "1"]
                    model.add(sum(sum_variables) >=
                              interval.lower *
                              parent_variable)
                    model.add(
                        sum(sum_variables) <= interval.upper * parent_variable)
                else:
                    model.add(sum(sum_variables) >=
                              interval.lower)
                    model.add(
                        sum(sum_variables) <= interval.upper)
                return

            # Loop through the range based on the current depth value in arr[depth]
            for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                current_indices.append(i)  # Add the current index to the list
                helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
                current_indices.pop()

        helper(0, [])


        for child in feature.children:
            old_list = parent_list.copy()
            create_assert_group_cardinality_cloning_csp(model, instance, child, old_list,
                                                                                  only_boolean_constants)


def getMaxCardinality(intervals: list[Interval]) -> int:
    max = 1
    for interval in intervals:
        if interval.upper >= max:
            max = interval.upper

    return max


def create_amount_of_children_for_group_instance_cardinality_cloning_csp(children:
                                                                list[Feature], indices, only_boolean_constants):

    sum_variables = []

    for feature in children:
        if only_boolean_constants or (not only_boolean_constants and len(feature.children) >= 1):
            for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                if len(indices) > 0:
                    sum_variables.append(variables[create_const_name(feature) + "_" +  "_".join(map(str, indices)) + "_" + str(i)])
                else:
                    sum_variables.append(variables[create_const_name(feature) + "_" + str(i)])
        else:
            sum_variables.append(variables[create_const_name(feature) + "_" + "_".join(map(str, indices))])


    return sum_variables

def create_amount_of_children_for_group_type_cardinality_cloning_csp(model: CpModel, children:
                                                                list[Feature], indices, only_boolean_constants):
    sum_variables = []

    for feature in children:
        if only_boolean_constants or (not only_boolean_constants and len(feature.children) >= 1):
            helper_variables = []
            for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                helper_variable = model.new_bool_var(create_const_name(feature) + "_" +
                                                     "_".join(map(str, indices)) + "_" + str(
                                                     i) + "_helper")
                helper_variables.append(helper_variable)
                if len(indices) > 0:
                    variable_name = create_const_name(feature) + "_" + "_".join(
                        map(str, indices)) + "_" + str(i)
                    model.add(variables[variable_name] > 0).only_enforce_if(helper_variable)
                    model.add(variables[variable_name] <= 0).only_enforce_if(helper_variable.Not())
                else:
                    variable_name = create_const_name(feature) + "_" + str(i)
                    model.add(variables[variable_name] > 0).only_enforce_if(helper_variable)
                    model.add(variables[variable_name] <= 0).only_enforce_if(helper_variable.Not())

            helper2 = model.new_bool_var(create_const_name(feature) + "_" +
                                                     "_".join(map(str, indices)) + "_helper2")
            model.add_at_least_one(helper_variables).only_enforce_if(helper2)
            model.add(sum(helper_variables) <= 0).only_enforce_if(helper2.Not())
            sum_variables.append(helper2)

        else:
            sum_variables.append(create_const_name(feature) + "_" + "_".join(map(str, indices)))


    return sum_variables