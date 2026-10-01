"""Guard the boundary between external results and local formalization coverage."""
import copy
import json
from pathlib import Path
import unittest

import literature


class LiteratureTests(unittest.TestCase):
    def test_published_result_is_not_local_formalization(self):
        paper = {'publication': 'Journal article', 'local_results': []}
        self.assertEqual(literature.coverage(paper, {}), 'pending')

    def test_complete_fragment_does_not_complete_the_paper(self):
        paper = {'local_results': [{'node': 'fragment', 'scope': 'Restricted theorem'}]}
        self.assertEqual(literature.coverage(paper, {'fragment': {'state': 'formalized'}}), 'partial')
        self.assertEqual(literature.coverage(paper, {'fragment': {'state': 'pending'}}), 'pending')

    def test_fragment_certificate_is_reported_without_covering_paper(self):
        paper = {'local_results': [{'node': 'fragment', 'scope': 'Restricted theorem'}]}
        records = {'fragment': {'state': 'formalized', 'blueprint': 'lem:fragment'}}
        certificates = {'fragment-cert': {'label': 'lem:fragment', 'module': 'solutions.Fragment'},
                        'unrelated': {'label': 'lem:other', 'module': 'solutions.Other'}}
        self.assertEqual(set(literature.supporting_certificates(paper, records, certificates)),
                         {'fragment-cert'})
        self.assertEqual(literature.coverage(paper, records), 'partial')

    def test_dangling_local_mapping_and_logical_arrow_are_rejected(self):
        catalog = json.loads((Path(__file__).parent / 'literature.json').read_text())
        records = {i['node']: {'state': 'formalized'} for p in catalog['papers'] for i in p['local_results']}
        literature.validate(catalog, records)
        damaged = copy.deepcopy(catalog)
        damaged['papers'][0]['local_results'][0]['node'] = 'nonexistent'
        with self.assertRaisesRegex(ValueError, 'invalid local result'):
            literature.validate(damaged, records)
        damaged = copy.deepcopy(catalog)
        damaged['diagram_edges'][0]['kind'] = 'implication'
        with self.assertRaisesRegex(ValueError, 'not proof implications'):
            literature.validate(damaged, records)
        damaged = copy.deepcopy(catalog)
        damaged['papers'][0]['target_declarations'] = [{'name': 'claim', 'source': 'formalization/Claim.lean'}]
        damaged['papers'][0].pop('target_review', None)
        with self.assertRaisesRegex(ValueError, 'scope review'):
            literature.validate(damaged, records)
        damaged = copy.deepcopy(catalog)
        damaged['priorities'][0]['papers'] = ['route:moment-map-cmh']
        with self.assertRaisesRegex(ValueError, 'source papers'):
            literature.validate(damaged, records)


if __name__ == '__main__':
    unittest.main()
