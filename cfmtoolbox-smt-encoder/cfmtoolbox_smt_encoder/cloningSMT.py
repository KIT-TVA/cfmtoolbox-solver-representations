from cfmtoolbox import CFM, Feature, Interval

from cfmtoolbox_smt_encoder.mulitsetSMT import create_const_name, create_assert_feature_group_instance_cardinality





def create_smt_cloning_encoding(cfm: CFM):
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_cloned_constants(cfm.root,1)
    encoding += create_assert_child_parent_connection_cloning(cfm.root)
    encoding += create_assert_feature_group_type_cardinality_cloning(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality_cloning(cfm.root)

    print(encoding)
    return encoding


def declare_cloned_constants(parent: Feature, parentMaxCardinality: int):
    constants = ""

    max = getMaxCardinality(parent.instance_cardinality.intervals)

    for i in range(1,parentMaxCardinality + 1):
        for j in range(1, max + 1):
            constants += "(declare-const " + create_const_name(parent) + "_" + str(i) + "_" + str(j) + " Bool)\n"

    for feature in parent.children:
        constants += declare_cloned_constants(feature, max)

    return constants

def create_assert_child_parent_connection_cloning(feature: Feature) -> str:
    childrenAssert = ""

    if feature.children:
        children = feature.children
        if feature.parent is None:
            childrenAssert += "(assert "
            childrenAssert += "(and "
            for feature in children:
                childrenAssert += create_assert_child_parent_connection_cloning(feature)

            childrenAssert += " )" # closing and
            childrenAssert += " )\n"  # closing assert
        else:
            childrenAssert += "(and "
            if feature.parent.parent is not None:
                grant_parent_cardinality = getMaxCardinality(feature.parent.parent.instance_cardinality.intervals)
            else:
                grant_parent_cardinality = 1
            for p in range(1, grant_parent_cardinality + 1):
                for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                    childrenAssert += "(and "
                    for feature in children:
                        for j in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
                            childrenAssert += "(ite "
                            childrenAssert += "(not " + create_const_name(feature.parent) + "_" + str(p) + "_" + str(i) + ") "
                            childrenAssert += "(= " + create_const_name(feature) + "_" + str(i) + "_" + str(j) + " false)"
                            childrenAssert += "(= " + "true"  + " true)"
                            childrenAssert += ") " # closing ite
                            childrenAssert += create_assert_child_parent_connection_cloning(feature)
                    childrenAssert += ")\n " # closing and
            childrenAssert += ")\n " #closing big and of else part


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
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            if len(feature.group_type_cardinality.intervals) > 1:
                assertStatement += "(or"
            for interval in feature.group_type_cardinality.intervals:

                assertStatement += "(and "
                assertStatement += "(>= "
                assertStatement += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, i)
                assertStatement += str(interval.lower)
                assertStatement += ")"
                if interval.upper is None:
                    assertStatement += "(= true true)"
                else:
                    assertStatement += "(<= "
                    assertStatement += create_amount_of_children_for_group_type_cardinality_cloning(feature.children, i)
                    assertStatement += str(interval.upper)
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
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            if len(feature.group_type_cardinality.intervals) > 1:
                assertStatement += "(or"
            for interval in feature.group_instance_cardinality.intervals:

                assertStatement += "(and "
                assertStatement += "(>= "
                assertStatement += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children, i)
                assertStatement += str(interval.lower)
                assertStatement += ")"
                if interval.upper is None:
                    assertStatement += "(= true true)"
                else:
                    assertStatement += "(<= "
                    assertStatement += create_amount_of_children_for_group_instance_cardinality_cloning(feature.children, i)
                    assertStatement += str(interval.upper)
                    assertStatement += ")"
                assertStatement += ")\n"  # closing and
            if len(feature.group_instance_cardinality.intervals) > 1:
                assertStatement += ")"  # closing or
        assertStatement += ")"  # closing outter and

        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_instance_cardinality_cloning(child)
    return assertStatement


def create_amount_of_children_for_group_instance_cardinality_cloning(children, root_instance):
    amount = ""

    amount += "(+ "
    for feature in children:
        for i in range(1, getMaxCardinality(feature.instance_cardinality.intervals) + 1):
            amount += "(ite "
            amount += " " + create_const_name(feature) + "_" + str(root_instance) + "_" + str(i) + " "
            amount += " 1 "
            amount += " 0 "
            amount += " ) "  # closing ite
    amount += " ) "  # closing +

    return amount