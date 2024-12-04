import unittest

from cfmtoolbox.plugins.json_import import import_json
from cfmtoolbox_smt_encoder import run_smt_solver_with_cloning_base_gap_detection


class TestCloningSMT(unittest.TestCase):



   def test_gaps_multiplayer_cloning_basic(self):
       file = open("../cfms/multiplayer.json", "rb")
       self.cfm = import_json(file.read())
       file.close()

       result = run_smt_solver_with_cloning_base_gap_detection(cfm=self.cfm)

       self.assertIn('Gap at: 5 in Feature: Team', result)
       for i in range(9,30):
           self.assertIn('Gap at: ' +  str(i) + ' in Feature: Team', result)

       self.assertIn('Gap at: 30 in Feature: Player', result)

if __name__ == '__main__':
    unittest.main()
