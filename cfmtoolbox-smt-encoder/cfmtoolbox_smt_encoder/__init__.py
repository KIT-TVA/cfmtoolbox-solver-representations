from pyexpat import features

from cfmtoolbox import app, CFM, Feature, Interval



@app.command()
def encode_to_smt_multiset(cfm: CFM) -> str:
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_constants(cfm.features)
    encoding += create_assert_child_parent_connection(cfm.root.children)
    encoding += create_assert_feature_group_type_cardinality(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality(cfm.root,Interval(1,1))

    print(encoding)
    return encoding


@app.command()
def encode_to_smt_cloning(cfm: CFM) -> str:
    print("Encoding CFM...")
    encoding = ""

    encoding += declare_constants(cfm.features)
    encoding += create_assert_child_parent_connection(cfm.root.children)
    encoding += create_assert_feature_group_type_cardinality(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality(cfm.root)

    print(encoding)
    return encoding



def create_assert_feature_group_type_cardinality(feature: Feature):
    assertStatement = ""
    if  feature.group_type_cardinality.intervals:
        assertStatement += "(assert "
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += "(or"
        for interval in feature.group_type_cardinality.intervals:

            assertStatement += "(and "
            assertStatement += "(>= "
            assertStatement += create_amount_of_children_for_group_type_cardinality(feature.children)
            assertStatement +=  str(interval.lower)
            assertStatement += ")"
            if interval.upper is None:
                assertStatement += "(= true true)"
            else:
                assertStatement += "(<= "
                assertStatement += create_amount_of_children_for_group_type_cardinality(feature.children)
                assertStatement += str(interval.upper)
                assertStatement += ")"
            assertStatement += ")" # closing and
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += ")" # closing or
        assertStatement += ")\n" # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_type_cardinality(child)
    return assertStatement

def create_amount_of_children_for_group_type_cardinality(features: list):

    amount = ""

    amount += "(+ "
    for feature in features:
        amount += "(ite "
        amount += "(>= " + create_const_name(feature) + " 1)"
        amount += " 1 "
        amount += " 0 "
        amount += " )"
    amount += " )"

    return amount

def create_sum_of_children_for_group_type_cardinality(features: list):

    sum = ""

    sum += "(+ "
    for feature in features:
        sum += create_const_name(feature)
        sum += " "
    sum += " )"

    return sum

def create_assert_feature_group_instance_cardinality(feature: Feature, parentCardinality: Interval):
    assertStatement = ""
    if feature.group_instance_cardinality.intervals:
        assertStatement += "(assert "
        if len(feature.group_instance_cardinality.intervals) > 1:
            assertStatement += "(or"
        for interval in feature.group_instance_cardinality.intervals:
            assertStatement += "(or "
            assertStatement += "(>= "
            assertStatement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assertStatement += " "
            assertStatement += str(interval.lower * parentCardinality.lower)
            assertStatement += ") "
            assertStatement += "(<= "
            assertStatement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assertStatement += " "
            assertStatement += str(interval.upper * parentCardinality.upper)
            assertStatement += ") "

        if len(feature.group_instance_cardinality.intervals) > 1:
            assertStatement += ")"  # closing or


    for interval in feature.group_instance_cardinality.intervals:
        for child in feature.children:
            assertStatement += create_assert_feature_group_instance_cardinality(child, interval)

    return assertStatement

def create_assert_child_parent_connection(features: list) -> str:
    childrenAssert = ""


    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            childrenAssert += "(assert "
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += create_assert_child_parent_connection(feature.children)

            childrenAssert += " )"
        else:
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += "(ite "
                childrenAssert += "(= " + create_const_name(feature.parent) + " 0)"
                childrenAssert += "(= " + create_const_name(feature) + " 0)"
                childrenAssert += "(>= " + create_const_name(feature) + " 0)"
                childrenAssert += ")"
                childrenAssert += create_assert_child_parent_connection(feature.children)
            childrenAssert += " )"

    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            childrenAssert += " )\n"

    return childrenAssert

def declare_constants(features: list) -> str:
    constants = ""

    for feature in features:
        constants += "(declare-const " + create_const_name(feature) +  " int)\n"

    return constants


def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name