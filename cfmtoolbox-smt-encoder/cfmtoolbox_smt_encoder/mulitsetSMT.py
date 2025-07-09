from cfmtoolbox import CFM, Feature, Interval, Constraint


global assertCount
global variableCount

def create_smt_multiset_encoding(cfm: CFM, sampling: bool):
    print("Encoding CFM...")
    encoding = ""
    global assertCount
    global variableCount
    assertCount = 0
    variableCount = 0
    encoding += declare_constants(cfm.features)
    #encoding += create_assert_child_parent_connection(cfm.root.children)
    encoding += create_assert_feature_group_type_cardinality(cfm.root,sampling)
    encoding += create_assert_group_type_cardinality_with_less_max_than_features(cfm.root)
    encoding += create_assert_feature_group_instance_cardinality(cfm.root)
    encoding += create_assert_feature_instance_cardinality(cfm.root)
    encoding += create_assert_constraints(cfm.constraints)
    print("Encoding complete.")

    print("Variable count: " + str(variableCount))
    print("Assert count: " + str(assertCount))
    #print(encoding)
    return encoding


def create_assert_feature_group_type_cardinality(feature: Feature,sampling: bool):
    assertStatement = ""
    global assertCount
    if feature.group_type_cardinality.intervals:
        assertCount += 1
        assertStatement += "(assert "
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += "(xor"
        for interval in feature.group_type_cardinality.intervals:
            assertStatement += "(ite "
            assertStatement += "(> " + create_const_name(feature) + " 0)"
            assertStatement += "(and "
            assertStatement += "(>= "
            assertStatement += create_amount_of_children_for_group_type_cardinality(
                feature.children, feature,sampling)
            assertStatement += str(interval.lower)
            assertStatement += ")"
            if interval.upper is None:
                assertStatement += "(= true true)"
            else:
                assertStatement += "(<= "
                assertStatement += create_amount_of_children_for_group_type_cardinality(
                    feature.children, feature,sampling)
                if sampling:
                    assertStatement += str(
                        interval.upper)
                else:
                    assertStatement += "(* " + create_const_name(feature) + " " + str(
                        interval.upper) + " )"
                assertStatement += ")"
            assertStatement += ")"  # closing and
            assertStatement += "(= true true))"
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += ")"  # closing or
        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_feature_group_type_cardinality(child,sampling)
    return assertStatement

def create_assert_group_type_cardinality_with_less_max_than_features(feature: Feature):
    assertStatement = ""
    global assertCount
    if feature.group_type_cardinality.intervals:
        assertCount += 1
        assertStatement += "(assert "
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += "(xor"
        for interval in feature.group_type_cardinality.intervals:
            assertStatement += "(and "
            assertStatement += "(>= "
            assertStatement += create_amount_of_children_for_group_type_cardinality(
                feature.children, feature, True)
            assertStatement += "(* "
            assertStatement += str(interval.lower)
            assertStatement += "(ite "
            assertStatement += "(> " + create_const_name(feature) + " 0)"
            assertStatement += " 1 0 )"
            assertStatement += ")"
            assertStatement += ")"
            if interval.upper is None:
                assertStatement += "(= true true)"
            else:
                assertStatement += "(<= "
                assertStatement += create_amount_of_children_for_group_type_cardinality(
                    feature.children, feature, True)
                assertStatement += "(* "
                assertStatement += str(interval.upper)
                assertStatement += "(ite "
                assertStatement += "(> " + create_const_name(feature) + " 0)"
                assertStatement += " 1 0 )"
                assertStatement += ")"
                assertStatement += ")"
            assertStatement += ")"  # closing and
        if len(feature.group_type_cardinality.intervals) > 1:
            assertStatement += ")"  # closing or
        assertStatement += ")\n"  # closing assert

    for child in feature.children:
        assertStatement += create_assert_group_type_cardinality_with_less_max_than_features(child)


    return assertStatement

def create_assert_constraints(constraints):
    assertStatement = ""
    global assertCount
    for constraint in constraints:
        assertCount += 1
        assertStatement += "(assert "
        assertStatement += "(ite "
        assertStatement += create_constraint_feature_to_intervals(constraint.first_cardinality.intervals, constraint.first_feature)
        if not constraint.require:
            assertStatement += "(not "

        assertStatement += create_constraint_feature_to_intervals(constraint.second_cardinality.intervals, constraint.second_feature)

        if not constraint.require:
            assertStatement += " )" # closing not

        assertStatement += "(= true true)"
        assertStatement += ")" #closing ite
        assertStatement += ")\n" # closing assert
    return assertStatement


def create_constraint_feature_to_intervals(intervals: list, feature: Feature):
    constraint = ""
    if len(intervals) > 1:
        constraint +=  "(or "
    for interval in intervals:
        constraint = "(and "
        constraint += "(<= "
        constraint += create_const_name(feature)
        constraint += " "
        constraint += str(interval.upper)
        constraint += ")"
        constraint += "(>= "
        constraint += create_const_name(feature)
        constraint +=  " "
        constraint += str(interval.lower)
        constraint += ")"
        constraint += ")" # closing and
    if len(intervals) > 1:
        constraint += ")" #closing or
    return constraint

def create_assert_feature_instance_cardinality(feature: Feature):
    assert_statement = ""
    global assertCount
    assertCount += 1
    assert_statement += "(assert "
    if len(feature.instance_cardinality.intervals) > 1:
        assert_statement += "(or"
    for interval in feature.instance_cardinality.intervals:
        assert_statement += "(and "
        assert_statement += "(>= "
        assert_statement += create_const_name(feature) + " "
        if feature.parent is not None:
            assert_statement += "(* " + str(interval.lower) + " " + create_const_name(feature.parent) + ")"
        else:
            assert_statement += str(interval.lower)
        assert_statement += ")"
        assert_statement += "(<= "
        assert_statement += create_const_name(feature) + " "
        if feature.parent is not None:
            assert_statement += "(* " + str(interval.upper) + " " + create_const_name(
                feature.parent) + ")"
        else:
            assert_statement += str(interval.upper)
        assert_statement += ") "
        assert_statement += ")" # closing and

    if len(feature.instance_cardinality.intervals) > 1:
        assert_statement += ")"  # closing or
    assert_statement += ")\n" # closing assert


    for child in feature.children:
        assert_statement += create_assert_feature_instance_cardinality(child)

    return assert_statement




def create_amount_of_children_for_group_type_cardinality(features: list, parent: Feature,
                                                         sampling:bool):
    amount = ""

    amount += "(+ "
    for feature in features:
        amount += "(ite "
        amount += "(>= " + create_const_name(feature) + " "
        if sampling:
            amount += "1"  # for sampling it is not necessary that there is a clone in every tree
            # but for maximization it is
        else:
            amount += create_const_name(parent) # for group type cardinality in multisets, it is only valid if the feature is in all subtrees -> if the lower and upper bound are equal this is necessary
        amount +=  ")"                          # for max bounded check this should not change anything
        amount += " 1 "
        amount += " 0 "
        amount += " )" # closing ite
    amount += " )" # closing +

    return amount


def create_sum_of_children_for_group_type_cardinality(features: list):
    sum = ""

    sum += "(+ "
    for feature in features:
        sum += create_const_name(feature)
        sum += " "
    sum += " )" # closing +

    return sum


def create_assert_feature_group_instance_cardinality(feature: Feature):
    assert_statement = ""
    global assertCount
    if feature.group_instance_cardinality.intervals:
        assertCount += 1
        assert_statement += "(assert "



        if len(feature.group_instance_cardinality.intervals) > 1:
            assert_statement += "(or"

        for interval in feature.group_instance_cardinality.intervals:
            assert_statement += "(and "
            assert_statement += "(>= "
            assert_statement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assert_statement += " "
           # assert_statement += " " + str(interval.lower * parentInterval.lower) + " "

            assert_statement += "(* " + str(interval.lower) + " " +  create_const_name(feature) + ")"   #str(interval.lower * parentInterval.lower)

            assert_statement += ") "
            assert_statement += "(<= "
            assert_statement += create_sum_of_children_for_group_type_cardinality(feature.children)
            assert_statement += " "
            #assert_statement += " " + str(interval.upper * parentInterval.upper) + " "
            assert_statement += "(* " + str(interval.upper) + " " + create_const_name(feature) + ")"  # str(interval.upper * parentInterval.upper)
            assert_statement += ") "
            assert_statement += ")" # closing and

        if len(feature.group_instance_cardinality.intervals) > 1:
            assert_statement += ")"  # closing or


        assert_statement += ")\n" # closing assert

    for child in feature.children:
        assert_statement += create_assert_feature_group_instance_cardinality(child)

    return assert_statement


def create_assert_child_parent_connection(features: list) -> str:
    childrenAssert = ""
    global assertCount
    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            assertCount += 1
            childrenAssert += "(assert "
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += create_assert_child_parent_connection(feature.children)

            childrenAssert += " )" # closing and
        else:
            childrenAssert += "(and "
            for feature in features:
                childrenAssert += "(ite "
                childrenAssert += "(= " + create_const_name(feature.parent) + " 0)"
                childrenAssert += "(= " + create_const_name(feature) + " 0)"
                childrenAssert += "(>= " + create_const_name(feature) + " 0)"
                childrenAssert += ")" # closing ite
                childrenAssert += create_assert_child_parent_connection(feature.children)
            childrenAssert += " )" #closind and

    if len(features) != 0:
        if features.__getitem__(0).parent.parent is None:
            childrenAssert += " )\n" # closing assert

    return childrenAssert


def declare_constants(features: list) -> str:
    constants = ""
    global  variableCount
    for feature in features:
        variableCount += 1
        constants += "(declare-const " + create_const_name(feature) + " Int)\n"

    return constants


def get_all_constants_of_CFM_mulitset(cfm: CFM):
    constant_list = []
    for feature in cfm.features:
        constant_list.append(create_const_name(feature))
    return constant_list

def create_const_name(feature: Feature) -> str:
    return "Feature_" + feature.name
