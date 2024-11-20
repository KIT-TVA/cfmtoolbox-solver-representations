from cfmtoolbox import CFM, Feature, Interval

from cfmtoolbox_smt_encoder.mulitsetSMT import create_const_name, create_assert_feature_group_instance_cardinality, \
    create_assert_constraints


def create_smt_cloning_encoding(cfm: CFM):
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_cloned_constants(cfm.root,1, declaration=True)
    encoding += "(assert (= " + create_const_name(cfm.root) + "_1_1 true))"
    encoding += create_assert_child_parent_connection_cloning(cfm.root)
    encoding += create_assert_feature_group_type_cardinality_cloning(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality_cloning(cfm.root)
    encoding += create_assert_feature_instance_cardinality_cloning(cfm.features)
    encoding += create_assert_constraints_cloning(cfm)



    print(encoding)
    return encoding


def declare_cloned_constants(parent: Feature, parentMaxCardinality: int, declaration: bool):
    constants = ""

    max = getMaxCardinality(parent.instance_cardinality.intervals)

    for i in range(1,parentMaxCardinality + 1):
        for j in range(1, max + 1):
            if declaration:
                constants += "(declare-const "
            constants += create_const_name(parent) + "_" + str(i) + "_" + str(j) + " "
            if declaration:
                constants += " Bool)\n"
    for feature in parent.children:
        constants += declare_cloned_constants(feature, max, declaration)

    return constants


def create_assert_child_parent_connection_cloning(feature: Feature) -> str:
    childrenAssert = ""

    if feature.children:
        children = feature.children
        if feature.parent is None:

            for feature in children:
                childrenAssert += "(assert "
                childrenAssert += "(and "
                childrenAssert += create_assert_child_parent_connection_cloning(feature)
                childrenAssert += ")"
                childrenAssert += " )\n"  # closing assert
        else:
            childrenAssert += "(and "
            if feature.parent.parent is not None:
                grant_parent_cardinality = getMaxCardinality(feature.parent.parent.instance_cardinality.intervals)
            else:
                grant_parent_cardinality = 1

            for p in range(1, grant_parent_cardinality + 1):
                for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                    childrenAssert += "(ite "
                    childrenAssert += "(= " + create_const_name(feature) + "_" + str(p) + "_" + str(
                        i) + " false) "
                    childrenAssert += "(and "
                    for child in children:
                        for j in range(1, getMaxCardinality(child.instance_cardinality.intervals) + 1):
                            childrenAssert += "(= " + create_const_name(child) + "_" + str(i) + "_" + str(j) + " false)"
                    childrenAssert += ") "
                    childrenAssert += "(= " + "true"  + " true)"
                    childrenAssert += ") " # closing ite
            childrenAssert += ")\n " #closing big and of else part
            for child in children:
                childrenAssert += create_assert_child_parent_connection_cloning(child)

    else:
        childrenAssert = "(= true true)"
    return childrenAssert



def getMaxCardinality(intervals: list[Interval]) -> int:
    max = 1
    for interval in intervals:
        if interval.upper >= max:
            max = interval.upper

    return max


def create_assert_feature_group_type_cardinality_cloning(feature: Feature):
    assertStatement = ""
    if feature.group_type_cardinality.intervals:
        assertStatement += "(assert "

        assertStatement += "(and "
        if feature.parent is not None:
            parent_cardinality = getMaxCardinality(feature.parent.instance_cardinality.intervals)
        else:
            parent_cardinality = 1

        for p in range(1, parent_cardinality + 1):
            for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                if len(feature.group_type_cardinality.intervals) > 1:
                    assertStatement += "(or"
                for interval in feature.group_type_cardinality.intervals:

                    assertStatement += "(and "
                    assertStatement += "(>= "
                    assertStatement += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, i)
                    assertStatement += "(ite " +  create_const_name(feature) + "_" + str(p) + "_" + str(
                        i)  + " " + str(interval.lower) + " " + "0)"
                    assertStatement += ")"
                    if interval.upper is None:
                        assertStatement += "(= true true)"
                    else:
                        assertStatement += "(<= "
                        assertStatement += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, i)
                        assertStatement += "(ite " + create_const_name(feature) + "_" + str(p) + "_" + str(
                            i) + " " + str(interval.upper) + " " + "0)"
                        assertStatement += ")"
                    assertStatement += ")\n"  # closing and
                if len(feature.group_type_cardinality.intervals) > 1:
                    assertStatement += ")"  # closing or
        assertStatement += ")" # closing outter and

        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_type_cardinality_cloning(child)
    return assertStatement


def create_amount_of_children_for_group_type_cardinality_cloning(children, root_instance):
    amount = ""

    amount += "(+ "
    for feature in children:
        amount += "(ite "
        if getMaxCardinality(feature.instance_cardinality.intervals) > 1:
            amount += "(or "
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            amount += " " + create_const_name(feature) + "_" + str(root_instance) + "_" + str(i) + " "
        if getMaxCardinality(feature.instance_cardinality.intervals) > 1:
            amount += ")" # closing or
        amount += " 1 "
        amount += " 0 "
        amount += " ) "  # closing ite
    amount += " ) "  # closing +

    return amount

def create_assert_feature_group_instance_cardinality_cloning(feature: Feature):
    assertStatement = ""
    if feature.group_instance_cardinality.intervals:
        assertStatement += "(assert "

        assertStatement += "(and "
        if feature.parent is not None:
            parent_cardinality = getMaxCardinality(feature.parent.instance_cardinality.intervals)
        else:
            parent_cardinality = 1

        for p in range(1, parent_cardinality + 1):
            for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                if len(feature.group_type_cardinality.intervals) > 1:
                    assertStatement += "(or"
                for interval in feature.group_instance_cardinality.intervals:

                    assertStatement += "(and "
                    assertStatement += "(>= "
                    assertStatement += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children, i)
                    assertStatement += "(ite " + create_const_name(feature) + "_" + str(p) + "_" + str(
                        i) + " " + str(interval.lower) + " " + "0)"
                    assertStatement += ")"
                    if interval.upper is None:
                        assertStatement += "(= true true)"
                    else:
                        assertStatement += "(<= "
                        assertStatement += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children, i)
                        assertStatement += "(ite " + create_const_name(feature) + "_" + str(p) + "_" + str(
                            i) + " " + str(interval.upper) + " " + "0)"
                        assertStatement += ")"
                    assertStatement += ")\n"  # closing and
                if len(feature.group_instance_cardinality.intervals) > 1:
                    assertStatement += ")"  # closing or
        assertStatement += ")"  # closing outer and

        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_instance_cardinality_cloning(child)
    return assertStatement


def create_amount_of_children_for_group_instance_cardinality_cloning(children, root_instance):
    amount = ""
    if not children:
        return amount
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += "(+ "
    for feature in children:
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            amount += "(ite "
            amount += " " + create_const_name(feature) + "_" + str(root_instance) + "_" + str(i) + " "
            amount += " 1 "
            amount += " 0 "
            amount += " ) "  # closing ite
    if len(children) > 1 or getMaxCardinality(children[0].instance_cardinality.intervals) > 1:
        amount += " ) "  # closing +

    return amount



def create_assert_feature_instance_cardinality_cloning(features: list[Feature]):
    assertStatement = "(assert "
    assertStatement += "(and "

    for feature in features:
        if feature.parent is None:
            parent_cardinality = 1
            grandparent_cardinality = 1
        else:
            parent_cardinality = getMaxCardinality(feature.parent.instance_cardinality.intervals)
            if feature.parent.parent is None:
                grandparent_cardinality = 1
            else:
                grandparent_cardinality = getMaxCardinality(feature.parent.parent.instance_cardinality.intervals)
        assertStatement += "(and "
        for p in range(1, grandparent_cardinality + 1):
            for i in range( 1, parent_cardinality + 1):
                assertStatement += "(or "
                for interval in feature.instance_cardinality.intervals:
                    sum_of_feature_instance = create_sum_of_feature_instance(feature, i)
                    assertStatement += "(and "
                    assertStatement += "(<= "
                    assertStatement += str(sum_of_feature_instance) + " "
                    if feature.parent is not None:
                        assertStatement += "(ite " + create_const_name(feature.parent) + "_" + str(p) + "_" + str(
                            i) + " " + str(interval.upper) + " " + "0)"
                    else:
                        assertStatement += str(interval.upper)
                    assertStatement += ") "
                    assertStatement += "(>= "
                    assertStatement += str(sum_of_feature_instance) + " "
                    if feature.parent is not None:
                        assertStatement += "(ite " + create_const_name(feature.parent) + "_" + str(p) + "_" + str(
                            i) + " " + str(interval.lower) + " " + "0)"
                    else:
                        assertStatement += str(interval.lower)
                    assertStatement += ")"
                    assertStatement += ")\n"
                assertStatement += ")\n"

        assertStatement += ") "  # closing and

    assertStatement += ") " # closing and
    assertStatement += ")\n" # closing  assert
    return assertStatement

def get_min_cardinality(intervals: list[Interval]) -> int:
    min = intervals[0].lower
    for interval in intervals:
        if interval.lower <= min:
            min = interval.lower

    return min

def create_sum_of_feature_instance(feature: Feature, parent_instance):
    sum_of_feature_instance = ""
    sum_of_feature_instance += "(+ "
    for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
        sum_of_feature_instance += "(ite "
        sum_of_feature_instance += "(= " + create_const_name(feature) + "_" + str(parent_instance) + "_" + str(i) + " true) "
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
        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.first_cardinality.intervals, constraint.first_feature)
        if not constraint.require:
            constraints_cloning += "(not "

        constraints_cloning += create_constraint_feature_to_intervals_cloning(constraint.second_cardinality.intervals, constraint.second_feature)

        if not constraint.require:
            constraints_cloning += " )" # closing not

        constraints_cloning += "(= true true)"
        constraints_cloning += ")" #closing ite
        constraints_cloning += ")\n" # closing assert

    return constraints_cloning

def create_constraint_feature_to_intervals_cloning(cardinality_intervals: list[Interval], feature: Feature):
    constraints_cloning = ""

    sum_assert = ""
    if getMaxCardinality(feature.parent.instance_cardinality.intervals) > 1:
        sum_assert += "(+ "
    for i in range(1, getMaxCardinality(feature.parent.instance_cardinality.intervals) + 1):
        sum_assert += create_sum_of_feature_instance(feature, i)
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

def get_all_constants_of_CFM_cloning(cfm: CFM):
    constants = declare_cloned_constants(cfm.root,1,False)
    constant_list = constants.split(" ")
    return constant_list