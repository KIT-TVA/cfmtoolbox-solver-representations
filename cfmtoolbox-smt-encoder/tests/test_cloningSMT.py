import unittest

from cfmtoolbox.plugins.json_import import import_json
from cfmtoolbox_smt_encoder.cloningSMT import create_smt_cloning_encoding


class TestCloningSMT(unittest.TestCase):

    def setUp(self):
        file = open("../cfms/test.json", "rb")
        self.cfm = import_json(file.read())
        file.close()

    def test_valid_smt_cloning_only_boolean_constants_encoding(self):
        result = create_smt_cloning_encoding(self.cfm,True)
        self.assertIsInstance(result, str)

    def test_smt_cloning_only_boolean_constants_encoding_constants(self):
        # Create few features in the CFM and check if they are present in the encoding.
        result = create_smt_cloning_encoding(self.cfm, True)
        self.assertIn('declare-const Feature_pizza_1 Bool', result)
        self.assertIn('declare-const Feature_dough_1 Bool', result)
        self.assertIn('declare-const Feature_sourdough_1_1 Bool', result)

    def test_smt_cloning_leaves_ints_encoding_constants(self):
        # Create few features in the CFM and check if they are present in the encoding.
        result = create_smt_cloning_encoding(self.cfm, False)
        self.assertIn('declare-const Feature_pizza_1 Bool', result)
        self.assertIn('declare-const Feature_dough_1 Bool', result)
        self.assertIn('declare-const Feature_sourdough_1 Int', result)

if __name__ == '__main__':
    unittest.main()
