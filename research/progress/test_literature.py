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


class LemmaMapTests(unittest.TestCase):
    SOURCE = (
        'theorem proved_one : True := trivial\n\n'
        '/-- doc -/\ntheorem open_one : True := by\n  sorry\n\n'
        'noncomputable def object_one : Nat := 0\n')

    def item(self, ident, names=(), relation='same', **extra):
        return {'id': ident, 'locator': ident, 'label': ident, 'statement': 's', 'uses': [],
                'relation': relation, 'declarations': [{'name': f'NS.{n}', 'source': 'formalization/A.lean'}
                                                       for n in names], **extra}

    def read(self, path):
        return self.SOURCE

    def test_states_follow_declarations_and_relation(self):
        state = lambda *a, **k: literature.lemma_state(self.item('x', *a, **k), self.read)
        self.assertEqual(state(), 'pending')
        self.assertEqual(state(['proved_one']), 'formalized')
        self.assertEqual(state(['proved_one', 'open_one']), 'partial')
        self.assertEqual(state(['proved_one'], relation='partial'), 'partial')
        self.assertEqual(state(['object_one'], relation='stronger'), 'improved')
        self.assertIsNone(literature.declaration_body(self.SOURCE, 'NS.proved'))

    def test_lemma_map_validation(self):
        def paper(items):
            return {'id': 'P', 'lemma_map': {'source_version': 'v1', 'source_url': 'https://x',
                                             'reviewed_on': '2026-10-02', 'items': items}}
        good = [self.item('a', ['proved_one']), self.item('b', main=True, uses=['a'])]
        self.assertEqual(set(literature.validate_lemma_map(paper(good), self.read)), {'a', 'b'})
        cases = {'exactly one main': [self.item('a')],
                 'unknown dependency': [self.item('a', main=True, uses=['z'])],
                 'not found': [self.item('a', ['missing'], main=True)],
                 'needs a note': [self.item('a', ['proved_one'], relation='stronger', main=True)]}
        for message, items in cases.items():
            with self.assertRaisesRegex(ValueError, message):
                literature.validate_lemma_map(paper(items), self.read)


if __name__ == '__main__':
    unittest.main()
