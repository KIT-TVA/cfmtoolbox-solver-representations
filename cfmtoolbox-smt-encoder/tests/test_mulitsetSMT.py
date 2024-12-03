import unittest

from cfmtoolbox import CFM
from cfmtoolbox.plugins.json_import import import_json
from cfmtoolbox_smt_encoder.mulitsetSMT import create_smt_multiset_encoding
from setuptools.config.pyprojecttoml import load_file


class TestMultiSetSMT(unittest.TestCase):

    def setUp(self):
        file = open("../cfms/test.json", "rb")
        self.cfm = import_json(file.read())
        file.close()

    def test_valid_smt_multiset_encoding(self):
        result = create_smt_multiset_encoding(self.cfm)
        self.assertIsInstance(result, str)

    def test_smt_multiset_encoding_constants(self):
        # Create few features in the CFM and check if they are present in the encoding.
        result = create_smt_multiset_encoding(self.cfm)
        self.assertIn('declare-const Feature_pizza Int', result)
        self.assertIn('declare-const Feature_dough Int', result)
        self.assertIn('declare-const Feature_sourdough Int', result)

    # Add more tests based on various scenarios like children-parent connection, 
    # instance cardinality, constraints etc.


if __name__ == "__main__":
    unittest.main()
