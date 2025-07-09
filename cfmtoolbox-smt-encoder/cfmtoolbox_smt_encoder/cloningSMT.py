
from cfmtoolbox import CFM, Feature, Interval

global assertCount
global variableCount

def create_smt_cloning_encoding(cfm: CFM,only_boolean_constants: bool):
    """
    :param cfm: An instance of the CFM object which represents a cardinality-based feature model.
                This model is used as the basis for creating the SMT (Satisfiability Modulo
                Theories) encoding.
    :param only_boolean_constants: A boolean flag indicating whether to only create boolean constant
                for every feature instance or int constants for the leave features.This can
                reduce the overhead of the encoding
    :return: A string that represents the SMT encoding of the provided CFM.
    """
    print("Encoding CFM...")
    global assertCount
    global variableCount
    assertCount = 0
    variableCount = 0
    encoding = ""
    encoding += declare_cloned_constants(cfm.root,[], declaration=True,
                                         only_boolean_constants=only_boolean_constants)
    #encoding += "(assert (= " + create_const_name(cfm.root) + "_1 true))"
    #encoding += create_assert_child_parent_connection_cloning(cfm.root,[],
    #
    #                                                          only_boolean_constants=only_boolean_constants)
    encoding += create_assert_feature_group_cardinality_cloning(cfm.root,[],
                                                                instance_cardinality=False,
                                                                only_boolean_constants=only_boolean_constants)
    encoding += create_assert_feature_group_cardinality_cloning(cfm.root,[],
                                                                instance_cardinality=True,
                                                                only_boolean_constants=only_boolean_constants)
    encoding += create_assert_feature_instance_cardinality_cloning(cfm.root,[],
                                                                   only_boolean_constants=only_boolean_constants)
    encoding += create_assert_constraints_cloning(cfm,only_boolean_constants=only_boolean_constants)

    print("Variable count: " + str(variableCount))
    print("Assert count: " + str(assertCount))
    #print(encoding)
    print("Encoding complete.")

    return encoding



def declare_cloned_constants(parent: Feature, parent_list: list[int], declaration: bool,
                             only_boolean_constants: bool):
    """
    :param parent: The feature node for which constants are being created.
    :param parent_list: A list representing the cardinalities of each parent node encountered in the recursion. Each integer in the list dictates how deeply nested loops should iterate.
    :param declaration: A boolean indicating whether the function should generate SMT declarations for constants. If True, it will add "(declare-const " to each constant's declaration.
    :param only_boolean_constants: A boolean flag used to determine the type of constants to declare. If True, only boolean constants are declared; otherwise, both integer and boolean constants may be generated.
            Integer Constants are only generated for the Leaves of the CFMs
    :return: A string containing the generated constant declarations in SMT-LIB format, based on the conditions and structure specified by the input parameters.
    """
    constants = ""
    max = getMaxCardinality(parent.instance_cardinality.intervals)
    global variableCount

    if parent.parent is None:
        for j in range(1, max + 1):
            if declaration:
                variableCount += 1
                constants += "(declare-const "
            constants += create_const_name(parent) + "_" + str(j)
            if declaration:
                constants += " Bool)\n"
    else:
        # if it is a leave then do not append the instance cardinality, because the last constant will be an integer
        if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):
            parent_list.append(max if (max != 0) else 1)


        # Define the recursive function that generates n nested loops
        def helper(depth, current_indices):
            constants = ""
            global variableCount
            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):
                # decides whether only the constants names are created or the declarations for the encoding
                if declaration:
                    variableCount += 1
                    constants += "(declare-const "
                if len(current_indices) > 0:
                    constants += create_const_name(parent) + "_" + "_".join(map(str, current_indices))
                else: constants += create_const_name(parent)
                if declaration:
                    # when it is a leave and not the base cloning approach then add Int datatype, else Bool
                    if only_boolean_constants or (not only_boolean_constants and len(parent.children) >= 1):
                        constants += " Bool)\n"
                    else:

                        constants += " Int)\n"
                return constants

            loop_code = ""
            # Loop through the range based on the current depth value in arr[depth]
            for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                current_indices.append(i)  # Add the current index to the list
                loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
                current_indices.pop()
            return loop_code

        constants += helper(0, [])


    for feature in parent.children:
        old_list = parent_list.copy()
        constants += declare_cloned_constants(feature, old_list, declaration,only_boolean_constants)


    return constants


def create_assert_child_parent_connection_cloning(feature: Feature, parent_list: list[int],
                                                  only_boolean_constants: bool) -> str:
    childrenAssert = ""
    global assertCount
    # when the feature has no children, no more asserts are created
    if feature.children:
        children = feature.children
        # if it is a root feature than there is no need for the parent child assert, because the root feature can never have cardinality zero
        if feature.parent is None:
            for feature in children:
                old_list = parent_list.copy()
                assertCount += 1
                childrenAssert += "(assert " # one assert for all parent child connection of a children of the root feature
                childrenAssert += "(and "
                childrenAssert += create_assert_child_parent_connection_cloning(feature, old_list,only_boolean_constants)
                childrenAssert += ")"
                childrenAssert += " )\n"  # closing assert
        else:
            max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
            parent_list.append(max_cardinality if (max_cardinality != 0) else 1)
            childrenAssert += "(and "
            # Define the recursive function that generates n nested loops
            def helper(depth, current_indices, children):
                asserts = ""
                # Base case: if we've reached the innermost level, execute the code
                if depth == len(parent_list):
                    asserts += "(ite "
                    asserts += "(= " + create_const_name(feature) + "_" + "_".join(map(str, current_indices)) + " false) "
                    asserts += "(and "
                    for child in children:
                        if only_boolean_constants or (not only_boolean_constants and len(child.children) >= 1):
                            for j in range(1, getMaxCardinality(child.instance_cardinality.intervals) + 1):
                                asserts += "(= " + create_const_name(child) + "_" + "_".join(map(str, current_indices)) + "_" + str(j) + " false)"
                        else:
                            asserts += "(= " + create_const_name(child) + "_" + "_".join(
                                map(str, current_indices))  + " 0)"
                    asserts += ") "
                    asserts += "(= " + "true" + " true)"
                    asserts += ") "  # closing ite
                    return asserts

                loop_code = ""
                # Loop through the range based on the current depth value in arr[depth]
                for i in range(1,
                               parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                    current_indices.append(i)  # Add the current index to the list
                    loop_code += helper(depth + 1, current_indices,children)  # Recurse to the next depth (next loop)
                    current_indices.pop()
                return loop_code

            childrenAssert += helper(0, [],children)
            childrenAssert += ")\n " #closing big and of else part
            for child in children:
                old_list = parent_list.copy()
                childrenAssert += create_assert_child_parent_connection_cloning(child, old_list,only_boolean_constants)

    else:
        childrenAssert = "(= true true)"
    return childrenAssert


def getMaxCardinality(intervals: list[Interval]) -> int:
    max = intervals[0].upper
    for interval in intervals:
        if interval.upper >= max:
            max = interval.upper

    return max


def create_assert_feature_group_cardinality_cloning(feature: Feature, parent_list: list[int], instance_cardinality: bool, only_boolean_constants: bool) -> str:
    assertStatement = ""
    assert_sum_or_amount = ""
    global assertCount
    if instance_cardinality:
        intervals = feature.group_instance_cardinality.intervals

    else:
        intervals = feature.group_type_cardinality.intervals

    if intervals and len(feature.children) != 0:
        if feature.parent is not None:
            max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
            parent_list.append(max_cardinality if (max_cardinality != 0) else 1)
        assertCount += 1
        assertStatement += "(assert "

        assertStatement += "(and "

        def helper(depth, current_indices):
            asserts = ""
            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):
                if len(intervals) > 1:
                    asserts += "(or"
                for interval in intervals:

                    asserts += "(and "
                    asserts += "(>= "
                    if instance_cardinality:
                        asserts += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children,indices=current_indices,only_boolean_constants=only_boolean_constants)
                    else:
                        asserts += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, indices=current_indices, only_boolean_constants=only_boolean_constants)
                    if feature.parent is not None:
                        asserts += "(ite " + create_const_name(feature) + ("_" if (len(
                            current_indices) > 0) else "") + "_".join(map(str, current_indices)) + " " + str(interval.lower) + " " + "0)"
                    else:
                        asserts += ("(ite " + create_const_name(feature) + "_" + "1" + " " + str(interval.lower) + " " + "0)")
                    asserts += ")"
                    if interval.upper is None:
                        asserts += "(= true true)"
                    else:
                        asserts += "(<= "
                        if instance_cardinality:
                            asserts += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children,indices=current_indices, only_boolean_constants=only_boolean_constants)

                        else:
                            asserts += create_amount_of_children_for_group_type_cardinality_cloning(feature.children,
                                                                                                    indices=current_indices,only_boolean_constants=only_boolean_constants)
                        if feature.parent is not None:
                            asserts += ("(ite " + create_const_name(feature) + ("_" if (len(current_indices) > 0) else "") + "_".join(
                                map(str, current_indices)) + " " + str(interval.upper) + " " + "0)")
                        else:
                            asserts += ("(ite " + create_const_name(feature) + "_" + "1" + " " + str(
                                interval.upper) + " " + "0)")
                        asserts += ")"
                    asserts += ")\n"  # closing and
                if len(intervals) > 1:
                    asserts += ")"  # closing or
                return asserts

            loop_code = ""
            # Loop through the range based on the current depth value in arr[depth]
            for i in range(1,
                           parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
                current_indices.append(i)  # Add the current index to the list
                loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
                current_indices.pop()
            return loop_code
        assertStatement += helper(0, [])
        assertStatement += ")" # closing outter and
        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        old_list = parent_list.copy()
        assertStatement += create_assert_feature_group_cardinality_cloning(child,old_list,instance_cardinality,only_boolean_constants)
    return assertStatement





def create_amount_of_children_for_group_type_cardinality_cloning(children, indices, only_boolean_constants):
    amount = ""

    amount += "(+ "
    for feature in children:
        maxCardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        maxCardinality = maxCardinality if (maxCardinality != 0) else 1
        if (only_boolean_constants or (not only_boolean_constants and len(feature.children) >=
                                       1)):
            amount += "(ite "
            if maxCardinality > 1:
                amount += "(or "
            for i in range(1, maxCardinality + 1):
                if len(indices) > 0:
                    amount += (" " + create_const_name(feature) + "_" + "_".join(map(str, indices))
                               + "_" + str(i) + " ")
                else:
                    amount += " " + create_const_name(feature) + "_" + str(i) + " "
            if maxCardinality > 1:
                amount += ")" # closing or
            amount += " 1 "
            amount += " 0 "
            amount += " ) "  # closing ite
        else:
            amount += "(ite "
            amount += ("(> " + create_const_name(feature) + ("_" if (len(indices) > 0) else "") +
                       "_".join(map(str, indices)) + " 0)")
            amount += " 1 "
            amount += " 0 "
            amount += " ) "  # closing ite
    amount += " ) "  # closing +

    return amount

def create_amount_of_children_for_group_instance_cardinality_cloning(children: list[Feature], indices, only_boolean_constants):
    amount = ""
    if not children:
        return amount
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += "(+ "
    for feature in children:
        maxCardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        maxCardinality = maxCardinality if (maxCardinality != 0) else 1
        if (only_boolean_constants or (not only_boolean_constants and len(feature.children) >=
                                       1)):
            for i in range(1, maxCardinality + 1):
                amount += "(ite "
                if len(indices) > 0:
                    amount += " " + create_const_name(feature) +  "_" + "_".join(map(str, indices)) + "_" + str(i) + " "
                else:
                    amount += " " + create_const_name(feature) + "_" + str(i) + " "
                amount += " 1 "
                amount += " 0 "
                amount += " ) "  # closing ite
        else:
            amount += " " + create_const_name(feature) + ("_" if (len(indices) > 0) else "") + "_".join(map(str, indices)) + " "
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += " ) "  # closing +

    return amount



def create_assert_feature_instance_cardinality_cloning(parent: Feature, parent_list: list[int],only_boolean_constants: bool):
    global assertCount
    assertCount += 1
    assertStatement = "(assert "
    assertStatement += "(and "



    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):
        asserts = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            asserts += "(or "
            for interval in parent.instance_cardinality.intervals:
                sum_of_feature_instance = create_sum_of_feature_instance(parent, current_indices, only_boolean_constants)
                asserts += "(and "
                asserts += "(<= "
                asserts += str(sum_of_feature_instance) + " "
                if parent.parent is not None:
                    if len(current_indices) > 0:
                        asserts += "(ite " + create_const_name(parent.parent) + "_" + "_".join(map(str, current_indices)) + " " + str(interval.upper) + " " + "0)"
                    else:
                        asserts += "(ite " + create_const_name(parent.parent) + "_" + "1" + " " + str(interval.upper) + " " + "0)"
                else:
                    asserts += str(interval.upper)
                asserts += ") "
                asserts += "(>= "
                asserts += str(sum_of_feature_instance) + " "
                if parent.parent is not None:
                    if len(current_indices) > 0:
                        asserts += "(ite " + create_const_name(parent.parent) + "_" + "_".join(map(str, current_indices)) + " " + str(interval.lower) + " " + "0)"
                    else:
                        asserts += "(ite " + create_const_name(parent.parent) + "_" + "1" + " " + str(
                            interval.lower) + " " + "0)"
                else:
                    asserts += str(interval.lower)
                asserts += ")"
                asserts += ")\n"
            asserts += ")\n"
            return asserts

        loop_code = ""
        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return loop_code

    assertStatement += helper(0, [])

    assertStatement += ") "  # closing and
    assertStatement += ")\n"  # closing  assert

    if parent.parent is not None:
        max_cardinality = getMaxCardinality(parent.instance_cardinality.intervals)
        parent_list.append(max_cardinality if max_cardinality != 0 else 1)
    for feature in parent.children:
        old_list = parent_list.copy()
        assertStatement += create_assert_feature_instance_cardinality_cloning(feature, old_list,only_boolean_constants)


    return assertStatement



def get_min_cardinality(intervals: list[Interval]) -> int:
    min = intervals[0].lower
    for interval in intervals:
        if interval.lower <= min:
            min = interval.lower

    return min

def create_sum_of_feature_instance(feature: Feature, indices,only_boolean_constants: bool):
    sum_of_feature_instance = ""
    sum_of_feature_instance += "(+ "
    if only_boolean_constants or (not only_boolean_constants and len(feature.children) >= 1):
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        max_cardinality = max_cardinality if max_cardinality != 0 else 1
        for i in range(1,max_cardinality  + 1):
            sum_of_feature_instance += "(ite "
            if len(indices) > 0:
                sum_of_feature_instance += "(= " + create_const_name(feature) + "_" + "_".join(map(str, indices)) + "_" + str(i) + " true) "
            else:
                sum_of_feature_instance += "(= " + create_const_name(feature) +  "_" + str(i) + " true) "
            sum_of_feature_instance += " 1 "
            sum_of_feature_instance += " 0 "
            sum_of_feature_instance += ")"  # closing ite
    else:
        sum_of_feature_instance += " " + create_const_name(feature) + ("_" if (len(indices) > 0) else "") + "_".join(map(str, indices)) + " "
    sum_of_feature_instance += ")"
    return sum_of_feature_instance

def create_assert_constraints_cloning(cfm: CFM, only_boolean_constants: bool):
    constraints_cloning = ""
    global assertCount
    for constraint in cfm.constraints:
        assertCount += 1
        constraints_cloning += "(assert "
        constraints_cloning += "(ite "
        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.first_cardinality.intervals, constraint.first_feature, cfm.root,only_boolean_constants)
        if not constraint.require:
            constraints_cloning += "(not "

        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.second_cardinality.intervals, constraint.second_feature, cfm.root,only_boolean_constants)

        if not constraint.require:
            constraints_cloning += " )" # closing not

        constraints_cloning += "(= true true)"
        constraints_cloning += ")" #closing ite
        constraints_cloning += ")\n" # closing assert

    return constraints_cloning

def create_constraint_feature_to_intervals_cloning(cardinality_intervals: list[Interval], feature: Feature, root: Feature,only_boolean_constants: bool):
    constraints_cloning = ""

    parent_list = create_parent_list_for_feature_by_name(root,feature.name, [])
    sum_assert = ""

    sum_assert += "(+ "

    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):
        asserts = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            asserts += create_sum_of_feature_instance(feature, indices=current_indices, only_boolean_constants=only_boolean_constants)
            return asserts

        loop_code = ""
        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return loop_code

    sum_assert += helper(0, [])

    sum_assert += ")"  # closing +

    if len(cardinality_intervals) > 1:
        constraints_cloning += "(or "

    for interval in cardinality_intervals:
        constraints_cloning += "(and "
        constraints_cloning += "(<= "
        constraints_cloning += sum_assert
        constraints_cloning += str(interval.upper)
        constraints_cloning += ")" #closing <=
        constraints_cloning += "(>= "
        constraints_cloning += sum_assert
        constraints_cloning += str(interval.lower)
        constraints_cloning += ")"  # closing >=
        constraints_cloning += ")" #closing and

    if len(cardinality_intervals) > 1:
        constraints_cloning += ")" # closing or

    return constraints_cloning


def create_parent_list_for_feature_by_name(feature: Feature, feature_name: str, parent_list: list[int]):
    if feature.name is feature_name:
        return parent_list
    else:
        if feature.parent is not None:
            parent_list.append(getMaxCardinality(feature.instance_cardinality.intervals) if
                               getMaxCardinality(feature.instance_cardinality.intervals) > 0 else 1)
        for child in feature.children:
            old_list = parent_list.copy()
            new_list = create_parent_list_for_feature_by_name(child, feature_name,old_list)
            if new_list is not None:
                return new_list


def add_constraint_to_remove_permutations(feature, parent_list: list[
    int], only_boolean_constants):
    assertStatement = ""

    def helper(depth, current_indices):
        assertStatement = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):

            if only_boolean_constants or (
                    not only_boolean_constants and len(feature.children) >= 2):
                assertStatement += "(assert (and"
                for i in range(2, getMaxCardinality(feature.instance_cardinality.intervals) + 1):

                        if len(current_indices) > 0:
                            assertStatement += "(>= " + create_const_name(feature) + "_" + "_".join(
                                map(str, current_indices)) + "_" + str(i-1) + "  " + create_const_name(feature) + "_" + "_".join(
                                map(str, current_indices)) + "_" + str(i) + ")"
                        else:
                            assertStatement += "(>= " + create_const_name(feature) + "_" + str(
                                i-1) + " " +  create_const_name(feature) + "_" +  str(i) + ")"

                assertStatement += "))\n"

            return assertStatement

        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[
                              depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            assertStatement += helper(depth + 1, current_indices)  # Recurse to the next depth (next
            # loop)
            current_indices.pop()
        return assertStatement

    assertStatement += helper(0, [])

    if feature.parent is not None:
        max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in feature.children:
        old_list = parent_list.copy()
        assertStatement += add_constraint_to_remove_permutations(feature, old_list,
                                                              only_boolean_constants)
    return assertStatement


def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name

def get_all_constants_of_CFM_cloning(cfm: CFM):
    constants = declare_cloned_constants(cfm.root,[1],False,False)
    constant_list = constants.split(" ")
    return constant_list

