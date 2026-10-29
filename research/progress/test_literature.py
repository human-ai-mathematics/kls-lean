"""Guard the boundary between external results and local formalization coverage."""
import copy
import json
from pathlib import Path
import unittest

import literature


class LiteratureTests(unittest.TestCase):
    def test_background_and_later_citations_are_not_presented_as_primary_papers(self):
        catalog = {'papers': [{'authors': 'Original authors', 'date': '1995',
                              'additional_sources': [
                                  {'url': 'https://example.org/notes', 'label': 'Later lecture notes',
                                   'role': 'background'},
                                  {'url': 'https://example.org/citation', 'label': 'Later discussion',
                                   'role': 'secondary citation'}]}]}
        text = '\n'.join(literature.supplementary_references(catalog))
        self.assertIn('[Later lecture notes](https://example.org/notes) (background)', text)
        self.assertIn('[Later discussion](https://example.org/citation) (secondary citation)', text)
        self.assertNotIn('additional primary source', text)

    def test_supplementary_references_require_an_explicit_source_role(self):
        catalog = json.loads((Path(__file__).parent / 'literature.json').read_text())
        records = {i['node']: {'state': 'formalized'} for p in catalog['papers'] for i in p['local_results']}
        paper = next(p for p in catalog['papers'] if p.get('additional_sources'))
        paper['additional_sources'][0]['role'] = 'primary by default'
        with self.assertRaisesRegex(ValueError, 'source role'):
            literature.validate(catalog, records)

    def test_url_only_links_in_an_older_selected_index_stay_unclassified(self):
        text = '\n'.join(literature.supplementary_references({'papers': [
            {'authors': 'Authors', 'date': '1995',
             'additional_sources': ['https://example.org/notes']}]}))
        self.assertIn('(unclassified)', text)
        self.assertNotIn('additional primary source', text)

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

    def test_only_a_registered_target_certificate_covers_a_paper(self):
        paper = {'local_results': [], 'target_certificate': 'thm:target'}
        self.assertEqual(literature.coverage(paper, {}, {}), 'pending')
        certificates = {'node': {'label': 'thm:target', 'module': 'solutions.Target'}}
        self.assertEqual(literature.coverage(paper, {}, certificates), 'formalized')
        self.assertEqual(literature.coverage({'local_results': []}, {}, certificates), 'pending')


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

    def test_hub_and_combined_diagram_require_main_theorem_certificate_but_register_keeps_all(self):
        def paper(ident, certificate):
            return {'id': ident, 'authors': ident, 'target_certificate': certificate,
                    'lemma_map': {'source_version': 'v1', 'source_url': 'https://example.org',
                                  'reviewed_on': '2026-10-19',
                                  'items': [self.item('support', ['proved_one']),
                                            self.item('main', ['proved_one'], main=True, uses=['support']),
                                            self.item('open', ['open_one'])]}}
        catalog = {'papers': [paper('Covered', 'thm:main'), paper('Supporting', 'thm:missing')]}
        certificates = {'target': {'label': 'thm:main'}, 'fragment': {'label': 'lem:support'}}
        hub = literature.render_lemma_hub(catalog, certificates, self.read)
        self.assertIn('### Covered (v1)', hub)
        self.assertNotIn('### Supporting', hub)
        self.assertIn('LITERATURE.md#paper-lemma-maps', hub)
        sections, diagram, papers = literature.render_lemma_maps(catalog, self.read, certificates)
        self.assertIn('### Supporting lemma map', '\n'.join(sections))
        self.assertIn('open_one', '\n'.join(sections))
        self.assertIn('Covered_main', diagram)
        self.assertNotIn('Supporting_', diagram)
        self.assertEqual(len(papers), 2)
        empty = literature.render_lemma_hub(catalog, {}, self.read)
        self.assertIn('No covered paper', empty)
        self.assertIn('LITERATURE.md#paper-lemma-maps', empty)


class ProofPathTests(unittest.TestCase):
    def setUp(self):
        self.source = 'theorem certificate : True := trivial\ntheorem conditional (h : False) : True := trivial\n'
        items = [
            {'id': 'T31', 'locator': 'Theorem 3.1', 'label': 'Criterion', 'statement': 'True',
             'uses': [], 'relation': 'same', 'main': True,
             'declarations': [{'name': 'Solutions.Cert.certificate', 'source': 'solutions/Cert.lean'}]},
            {'id': 'T11', 'locator': 'Theorem 1.1', 'label': 'Assembly', 'statement': 'True',
             'uses': ['T31'], 'relation': 'partial',
             'declarations': [{'name': 'NS.conditional', 'source': 'formalization/Conditional.lean'}]},
        ]
        self.catalog = {'papers': [{'id': 'P', 'authors': 'Authors', 'url': 'https://example.org',
                                   'lemma_map': {'source_version': 'v1', 'source_url': 'https://example.org',
                                                 'reviewed_on': '2026-10-12', 'items': items}}],
                        'proof_path': {'source': 'P', 'steps': [
                            {'paper': 'P', 'item': 'T31', 'entries': ['Solutions.Cert.certificate'],
                             'boundary': 'Taylor hypothesis retained.', 'certificate': 'cert:criterion'},
                            {'paper': 'P', 'item': 'T11', 'entries': ['NS.conditional'],
                             'boundary': 'Universal input remains open.'}]}}
        self.certificates = {'cert:criterion': {'module': 'solutions.Cert',
                                               'declaration': 'Solutions.Cert.certificate'}}

    def render(self):
        return literature.render_proof_path(self.catalog, self.certificates, lambda _: self.source)

    def test_conditional_assembly_is_partial_and_source_certificate_keeps_its_boundary(self):
        text = self.render()
        self.assertIn('✓ Formalized in Lean', text)
        self.assertIn('◐ Partial or statement only', text)
        self.assertIn('Taylor hypothesis retained.', text)
        self.assertIn('Universal input remains open.', text)
        self.assertIn('[Certificate](../../solutions/Cert.lean)', text)

    def test_entries_and_certificates_cannot_escape_the_item_map(self):
        self.catalog['proof_path']['steps'][0]['entries'] = ['NS.unrelated']
        with self.assertRaisesRegex(ValueError, 'canonical lemma map'):
            self.render()
        self.catalog['proof_path']['steps'][0]['entries'] = ['Solutions.Cert.certificate']
        self.certificates['cert:criterion']['declaration'] = 'NS.unrelated'
        with self.assertRaisesRegex(ValueError, 'not registered'):
            self.render()

    def test_missing_boundary_and_duplicate_steps_are_rejected(self):
        self.catalog['proof_path']['steps'][0]['boundary'] = ''
        with self.assertRaisesRegex(ValueError, 'input boundary'):
            self.render()
        self.catalog['proof_path']['steps'][0]['boundary'] = 'Retained.'
        self.catalog['proof_path']['steps'].append(self.catalog['proof_path']['steps'][0])
        with self.assertRaisesRegex(ValueError, 'Duplicate'):
            self.render()


if __name__ == '__main__':
    unittest.main()
