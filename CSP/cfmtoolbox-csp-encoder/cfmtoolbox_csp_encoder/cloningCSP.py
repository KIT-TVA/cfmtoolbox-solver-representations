import re

from cfmtoolbox import CFM, Feature, Interval, Constraint
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
    print("Big M: " + str(big_m))
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


    create_assert_constraints_cloning_csp(model,cfm.constraints,cfm.root,
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


def getMinCardinality(intervals: list[Interval]) -> int:
    if len(intervals) == 0:
        return 0
    else:
        min_lowerbound = intervals[0].lower
        for interval in intervals:
            if interval.lower < min_lowerbound:
                min_lowerbound = interval.lower
        return min_lowerbound


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
            #print(variables[create_const_name(feature) + "_" + "_".join(map(str, indices))])

    return sum_variables

def create_amount_of_children_for_group_type_cardinality_cloning_csp(model: CpModel, children:
                                                                list[Feature], indices, only_boolean_constants):
    sum_variables = []

    for feature in children:
        if only_boolean_constants or (not only_boolean_constants and len(feature.children) >= 1):
            boolean_variables = []
            for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):

                if len(indices) > 0:
                    variable_name = create_const_name(feature) + "_" + "_".join(
                        map(str, indices)) + "_" + str(i)
                    boolean_variables.append(variables[variable_name])
                else:
                    variable_name = create_const_name(feature) + "_" + str(i)
                    boolean_variables.append(variables[variable_name])

            helper2 = model.new_bool_var(create_const_name(feature) + "_" +
                                                     "_".join(map(str, indices)) + "_helper2")
            model.add_at_least_one(boolean_variables).only_enforce_if(helper2)
            model.add(sum(boolean_variables) == 0).only_enforce_if(helper2.Not())
            sum_variables.append(helper2)

        else:
            feature_int_variable = variables[create_const_name(feature) + "_" + "_".join(map(str,
                                                                                      indices))]
            helper_int = model.new_bool_var(create_const_name(feature) + "_" +
                                         "_".join(map(str, indices)) + "_helper_int")
            model.add(feature_int_variable > 0).only_enforce_if(helper_int)
            model.add(feature_int_variable == 0).only_enforce_if(helper_int.Not())
            sum_variables.append(helper_int)

    return sum_variables


def create_assert_constraints_cloning_csp(model: CpModel, constraints: list[Constraint],
                                          root: Feature,
                                          only_boolean_constants):
    for i, constraint in enumerate(constraints):
        first_interval_constant = model.new_bool_var("constraint_first_interval_literal_" +
                                                     str(i))
        first_interval = constraint.first_cardinality.intervals.__getitem__(0)

        variables["constraint_first_interval_literal_" +
                  str(i)] = first_interval_constant

        sum_variables = create_constraint_feature_to_intervals_cloning(root,
                                                                       constraint.first_feature,only_boolean_constants)

        model.add(sum(sum_variables) >=
                  first_interval.lower).only_enforce_if(first_interval_constant)
        model.add(sum(sum_variables) <=
                  first_interval.upper).only_enforce_if(first_interval_constant)

        out_of_range_low = model.NewBoolVar('out_of_range_low')
        out_of_range_high = model.NewBoolVar('out_of_range_high')

        # Define the conditions for the OR
        model.Add(sum(sum_variables) < first_interval.lower).only_enforce_if(out_of_range_low)
        model.Add(sum(sum_variables) > first_interval.upper).only_enforce_if(out_of_range_high)

        model.AddBoolOr([out_of_range_low, out_of_range_high]).only_enforce_if(
            first_interval_constant.Not())

        second_interval_constant = model.new_bool_var("constraint_second_interval_literal_" +
                                                      str(i))
        variables["constraint_second_interval_literal_" +
                  str(i)] = second_interval_constant

        sum_variables2 = create_constraint_feature_to_intervals_cloning(root,
                                                                       constraint.second_feature,
                                                                        only_boolean_constants)

        second_interval = constraint.second_cardinality.intervals.__getitem__(0)
        model.add(sum(sum_variables2) >=
                  second_interval.lower).only_enforce_if(second_interval_constant)
        model.add(sum(sum_variables2) <= second_interval.upper).only_enforce_if(
            second_interval_constant)

        out_of_range_low_2 = model.NewBoolVar('out_of_range_low')
        out_of_range_high_2 = model.NewBoolVar('out_of_range_high')

        model.Add(sum(sum_variables2) < second_interval.lower).only_enforce_if(out_of_range_low_2)
        model.Add(sum(sum_variables2) > second_interval.upper).only_enforce_if(
            out_of_range_high_2)

        model.AddBoolOr([out_of_range_low_2, out_of_range_high_2]).only_enforce_if(
            second_interval_constant.Not())

        if constraint.require:
            model.add_implication(first_interval_constant, second_interval_constant)
        else:
            model.add(first_interval_constant + second_interval_constant <= 1)


def create_constraint_feature_to_intervals_cloning(root: Feature,
                                                   feature: Feature,only_boolean_constants: bool):


    parent_list = create_parent_list_for_feature_by_name(root, feature.name, [])
    sum_variables = []
    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):
        asserts = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            for variable in create_sum_of_feature_instance(feature, indices=current_indices,
                                            only_boolean_constants=only_boolean_constants):
                sum_variables.append(variable)
            return asserts

        loop_code = ""
        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return loop_code

    helper(0, [])

    return sum_variables


def create_parent_list_for_feature_by_name(feature: Feature, feature_name: str, parent_list: list[int]):
    if feature.name is feature_name:
        return parent_list
    else:
        if feature.parent is not None:
            parent_list.append(getMaxCardinality(feature.instance_cardinality.intervals))
        for child in feature.children:
            old_list = parent_list.copy()
            new_list = create_parent_list_for_feature_by_name(child, feature_name,old_list)
            if new_list is not None:
                return new_list


def get_all_cloned_variables():
    return variables.values()

def add_constraint_to_remove_permutations(model, feature,parent_list: list[
    int], only_boolean_constants):


    def helper(depth, current_indices):

        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):

            if only_boolean_constants or (
                    not only_boolean_constants and len(feature.children) >= 1):
                for i in range(2, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                    if feature.parent is not None:
                        if len(current_indices) > 0:
                            parent_variable = variables[
                                create_const_name(feature.parent) + "_" + "_".join(
                                    map(str, current_indices))]
                            model.Add(variables[create_const_name(feature) + "_" + "_".join(
                                map(str, current_indices)) + "_" + str(i - 1)] >= variables[
                                          create_const_name(feature) + "_" + "_".join(
                                              map(str, current_indices)) + "_" + str(
                                              i)]).only_enforce_if(parent_variable)
                        else:
                            parent_variable = variables[create_const_name(
                                feature.parent) + "_" + "1"]
                            model.Add(variables[create_const_name(feature) + "_" +
                                                str(i - 1)] >= variables[
                                          create_const_name(feature) + "_" +
                                          str(i)]).only_enforce_if(parent_variable)
                    else:
                        if len(current_indices) > 0:
                            model.Add(variables[create_const_name(feature) + "_" + "_".join(
                                map(str, current_indices)) + "_" + str(i-1)] >= variables[
                                create_const_name(feature) + "_" + "_".join(
                                map(str, current_indices)) + "_" + str(i)])
                        else:
                            model.Add(variables[create_const_name(feature) + "_" +
                                                           str(i-1)] >=  variables[create_const_name(feature) + "_" +
                                                           str(i)])

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
        add_constraint_to_remove_permutations(model, feature, old_list, only_boolean_constants)


def constraint_to_remove_symmetry(model, secondlevelFeatures: list[Feature]):

    for feature in secondlevelFeatures:

        instance_interval = feature.instance_cardinality.intervals
        if getMaxCardinality(instance_interval) > 1:
            helper_variables = []
            minCardinality = getMinCardinality(instance_interval) if getMinCardinality(
                instance_interval) >= 1 else 1
            if feature.children is not None:
                for i in range(minCardinality,
                               getMaxCardinality(instance_interval)):
                    helper_variables = []

                    helper_variables.append(create_symmetry_constraint_for_symmetry(model,
                                                                                    feature,[],i))
                    helper_variables = flatten(helper_variables)

                    parent1 = variables[ create_const_name(feature) + "_" + str(i)]
                    parent2 = variables[ create_const_name(feature) + "_" + str(i + 1)]
                    model.add_at_least_one(helper_variables).only_enforce_if([parent1, parent2])
            else:
                helper_variables.append(create_symmetry_constraint_for_symmetry(model, feature,
                                                                                [],1))
                helper_variables = flatten(helper_variables)
                parent = variables[create_const_name(feature) + "_" + str(1)]

                model.add_at_least_one(helper_variables).only_enforce_if(parent)



def create_symmetry_constraint_for_symmetry(model, feature, parentCloneList: list[int],
                                            parent: int):
    helper_list = []

    if parentCloneList != []:

        variable_name = "symmetry_" + feature.name + "_" + str(parent) +  "_" +  "_".join(map(str,
                                                                               parentCloneList))
        variable = model.new_bool_var(variable_name)
        variables[variable_name] = variable


        helper_list.append(variable)
        if len(parentCloneList) > 0:

            variableParent1 = variables[
                create_const_name(feature) + "_" + str(parent) + "_" + "_".join(
                    map(str,
                        parentCloneList))]
            variableParent2 = variables[create_const_name(feature) + "_" + str(parent + 1) + "_" +
                                        "_".join(
                                            map(str, parentCloneList))]
        else:
            variableParent1 = variables[create_const_name(feature) + "_" + str(parent)]
            variableParent2 = variables[create_const_name(feature) + "_" + str(parent + 1)]
        model.Add(variableParent1 != variableParent2).only_enforce_if(variable)
        model.Add(variableParent1 == variableParent2).only_enforce_if(variable.Not())



    for child in feature.children:
        child_instance_interval = child.instance_cardinality.intervals
        minCardinality = getMinCardinality(child_instance_interval) if getMinCardinality(
            child_instance_interval) >= 1 else 1
        if child.children:

            for i in range(minCardinality,getMaxCardinality(child_instance_interval) + 1):

                parentList = parentCloneList.copy()
                parentList.append(i)
                helper_list.append(create_symmetry_constraint_for_symmetry(model, child,
                                                                           parentList,
                                                                           parent))
        else:
            parentList = parentCloneList.copy()
            helper_list.append(create_symmetry_constraint_for_symmetry(model, child,
                                                                       parentList,parent))

    return helper_list



def get_all_clones_of_feature(feature_name: str):
    list_of_clones = []
    for name,clone in variables.items():
        match = re.split(r"Feature_", name)
        if len(match) >= 2:
            name = match[1]
            if bool(re.search('[a-zA-Z]', name)):
                name = re.split(r'_', match[1])
                if feature_name == name[0]:
                    list_of_clones.append(clone)
            else:
                name = re.split(r'_', match[1])
                if feature_name == name[0]:
                    list_of_clones.append(clone)
    #print(list_of_clones)
    return list_of_clones


def flatten(lst):
    flat = []
    for item in lst:
        if isinstance(item, list):
            flat.extend(flatten(item))  # Recursive call
        else:
            flat.append(item)
    return flat
