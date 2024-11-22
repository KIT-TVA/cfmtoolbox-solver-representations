from audioop import reverse

from cfmtoolbox import CFM, Feature, Interval

from cfmtoolbox_smt_encoder.mulitsetSMT import create_const_name, create_assert_feature_group_instance_cardinality, \
    create_assert_constraints


def create_smt_cloning_encoding(cfm: CFM):
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_cloned_constants(cfm.root,[], declaration=True)
    encoding += "(assert (= " + create_const_name(cfm.root) + "_1 true))"
    encoding += create_assert_child_parent_connection_cloning(cfm.root,[])
    encoding += create_assert_feature_group_cardinality_cloning(cfm.root,[],instance_cardinality=False)
    encoding += create_assert_feature_group_cardinality_cloning(cfm.root,[], instance_cardinality=True)
    encoding += create_assert_feature_instance_cardinality_cloning(cfm.root,[])
    encoding += create_assert_constraints_cloning(cfm)



    print(encoding)
    return encoding



def declare_cloned_constants(parent: Feature, parent_list: list[int], declaration: bool):
    constants = ""
    max = getMaxCardinality(parent.instance_cardinality.intervals)
    if parent.parent is None:
        for j in range(1, max + 1):
            if declaration:
                constants += "(declare-const "
            constants += create_const_name(parent) + "_" + str(j) + " "
            if declaration:
                constants += " Bool)\n"
    else:
        parent_list.append(max)

        # Define the recursive function that generates n nested loops
        def helper(depth, current_indices):
            constants = ""
            # Base case: if we've reached the innermost level, execute the code
            if depth == len(parent_list):
                if declaration:
                    constants += "(declare-const "
                constants += create_const_name(parent) + "_" + "_".join(map(str, current_indices)) + " "
                if declaration:
                    constants += " Bool)\n"
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
        constants += declare_cloned_constants(feature, old_list, declaration)

    return constants


    #max = getMaxCardinality(parent.instance_cardinality.intervals)
    #for parent in parentList:
    #    for p in range(1,parent + 1):
    #            for j in range(1, max + 1):
    #                if declaration:
    #                    constants += "(declare-const "
    #                constants += create_const_name(parent) + "_" + str(i) + "_" + str(j) + " "
     #               if declaration:
      #                  constants += " Bool)\n"



def create_assert_child_parent_connection_cloning(feature: Feature, parent_list: list[int]) -> str:
    childrenAssert = ""

    if feature.children:
        children = feature.children
        if feature.parent is None:
            for feature in children:
                old_list = parent_list.copy()
                childrenAssert += "(assert "
                childrenAssert += "(and "
                childrenAssert += create_assert_child_parent_connection_cloning(feature, old_list)
                childrenAssert += ")"
                childrenAssert += " )\n"  # closing assert
        else:
            max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
            parent_list.append(max_cardinality)
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
                        for j in range(1, getMaxCardinality(child.instance_cardinality.intervals) + 1):
                            asserts += "(= " + create_const_name(child) + "_" + "_".join(map(str, current_indices)) + "_" + str(j) + " false)"
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
                childrenAssert += create_assert_child_parent_connection_cloning(child, old_list)

    else:
        childrenAssert = "(= true true)"
    return childrenAssert


def getMaxCardinality(intervals: list[Interval]) -> int:
    max = 1
    for interval in intervals:
        if interval.upper >= max:
            max = interval.upper

    return max


def create_assert_feature_group_cardinality_cloning(feature: Feature, parent_list: list[int], instance_cardinality: bool):
    assertStatement = ""
    assert_sum_or_amount = ""

    if instance_cardinality:
        intervals = feature.group_instance_cardinality.intervals

    else:
        intervals = feature.group_type_cardinality.intervals

    if intervals:
        if feature.parent is not None:
            max_cardinality = getMaxCardinality(feature.instance_cardinality.intervals)
            parent_list.append(max_cardinality)
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
                        asserts += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children,indices=current_indices)
                    else:
                        asserts += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, indices=current_indices)
                    if feature.parent is not None:
                        asserts += ("(ite " + create_const_name(feature) + "_" + "_".join(map(str, current_indices)) + " " + str(interval.lower) + " " + "0)")
                    else:
                        asserts += ("(ite " + create_const_name(feature) + "_" + "1" + " " + str(interval.lower) + " " + "0)")
                    asserts += ")"
                    if interval.upper is None:
                        asserts += "(= true true)"
                    else:
                        asserts += "(<= "
                        if instance_cardinality:
                            asserts += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children,indices=current_indices)

                        else:
                            asserts += create_amount_of_children_for_group_type_cardinality_cloning(feature.children,
                                                                                                    indices=current_indices)
                        if feature.parent is not None:
                            asserts += ("(ite " + create_const_name(feature) + "_" + "_".join(
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
        assertStatement += create_assert_feature_group_cardinality_cloning(child,old_list,instance_cardinality)
    return assertStatement





def create_amount_of_children_for_group_type_cardinality_cloning(children, indices):
    amount = ""

    amount += "(+ "
    for feature in children:
        amount += "(ite "
        if getMaxCardinality(feature.instance_cardinality.intervals) > 1:
            amount += "(or "
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            if len(indices) > 0:
                amount += " " + create_const_name(feature) + "_" +  "_".join(map(str, indices)) + "_" + str(i) + " "
            else:
                amount += " " + create_const_name(feature) + "_" + str(i) + " "
        if getMaxCardinality(feature.instance_cardinality.intervals) > 1:
            amount += ")" # closing or
        amount += " 1 "
        amount += " 0 "
        amount += " ) "  # closing ite
    amount += " ) "  # closing +

    return amount

def create_amount_of_children_for_group_instance_cardinality_cloning(children: list[Feature], indices):
    amount = ""
    if not children:
        return amount
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += "(+ "
    for feature in children:
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            amount += "(ite "
            if len(indices) > 0:
                amount += " " + create_const_name(feature) + "_" +  "_".join(map(str, indices)) + "_" + str(i) + " "
            else:
                amount += " " + create_const_name(feature) + "_" + str(i) + " "
            amount += " 1 "
            amount += " 0 "
            amount += " ) "  # closing ite
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += " ) "  # closing +

    return amount



def create_assert_feature_instance_cardinality_cloning(parent: Feature, parent_list: list[int]):
    assertStatement = "(assert "
    assertStatement += "(and "



    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):
        asserts = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            asserts += "(or "
            for interval in parent.instance_cardinality.intervals:
                sum_of_feature_instance = create_sum_of_feature_instance(parent, current_indices)
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

    if parent.parent is not None:
        max_cardinality = getMaxCardinality(parent.instance_cardinality.intervals)
        parent_list.append(max_cardinality)
    for feature in parent.children:
        old_list = parent_list.copy()
        assertStatement += create_assert_feature_instance_cardinality_cloning(feature, old_list)

    assertStatement += ") " # closing and
    assertStatement += ")\n" # closing  assert
    return assertStatement



def get_min_cardinality(intervals: list[Interval]) -> int:
    min = intervals[0].lower
    for interval in intervals:
        if interval.lower <= min:
            min = interval.lower

    return min

def create_sum_of_feature_instance(feature: Feature, indices):
    sum_of_feature_instance = ""
    sum_of_feature_instance += "(+ "
    for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
        sum_of_feature_instance += "(ite "
        if len(indices) > 0:
            sum_of_feature_instance += "(= " + create_const_name(feature) + "_" + "_".join(map(str, indices)) + "_" + str(i) + " true) "
        else:
            sum_of_feature_instance += "(= " + create_const_name(feature) +  "_" + str(i) + " true) "
        sum_of_feature_instance += " 1 "
        sum_of_feature_instance += " 0 "
        sum_of_feature_instance += ")"  # closing ite
    sum_of_feature_instance += ")"
    return sum_of_feature_instance

def create_assert_constraints_cloning(cfm: CFM):
    constraints_cloning = ""
    for constraint in cfm.constraints:
        constraints_cloning += "(assert "
        constraints_cloning += "(ite "
        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.first_cardinality.intervals, constraint.first_feature, cfm.root)
        if not constraint.require:
            constraints_cloning += "(not "

        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.second_cardinality.intervals, constraint.second_feature, cfm.root)

        if not constraint.require:
            constraints_cloning += " )" # closing not

        constraints_cloning += "(= true true)"
        constraints_cloning += ")" #closing ite
        constraints_cloning += ")\n" # closing assert

    return constraints_cloning

def create_constraint_feature_to_intervals_cloning(cardinality_intervals: list[Interval], feature: Feature, root: Feature):
    constraints_cloning = ""

    parent_list = create_parent_list_for_feature_by_name(root,feature.name, [])
    sum_assert = ""
    if getMaxCardinality(feature.parent.instance_cardinality.intervals) > 1:
        sum_assert += "(+ "

    # Define the recursive function that generates n nested loops
    def helper(depth, current_indices):
        asserts = ""
        # Base case: if we've reached the innermost level, execute the code
        if depth == len(parent_list):
            asserts += create_sum_of_feature_instance(feature, indices=current_indices)
            return asserts

        loop_code = ""
        # Loop through the range based on the current depth value in arr[depth]
        for i in range(1, parent_list[depth] + 1):  # arr[depth] defines how many times the loop at this level runs
            current_indices.append(i)  # Add the current index to the list
            loop_code += helper(depth + 1, current_indices)  # Recurse to the next depth (next loop)
            current_indices.pop()
        return loop_code

    sum_assert += helper(0, [])
    if getMaxCardinality(feature.parent.instance_cardinality.intervals) > 1:
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
            parent_list.append(getMaxCardinality(feature.instance_cardinality.intervals))
        for child in feature.children:
            old_list = parent_list.copy()
            new_list = create_parent_list_for_feature_by_name(child, feature_name,old_list)
            if new_list is not None:
                return new_list




def get_all_constants_of_CFM_cloning(cfm: CFM):
    constants = declare_cloned_constants(cfm.root,1,False)
    constant_list = constants.split(" ")
    return constant_list