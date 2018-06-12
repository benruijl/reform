# -*- coding: utf-8 -*-
import re
import sys

from sphinx import addnodes
from sphinx.domains import Domain, ObjType
from sphinx.locale import l_, _
from sphinx.directives import ObjectDescription
from sphinx.roles import XRefRole
from sphinx.util.nodes import make_refnode
from sphinx.util.docfields import Field, TypedField


def setup(sphinx):
    sphinx.add_domain(ReFORMDomain)


class ReFORMMarkup(ObjectDescription):
    """
    Description of generic reFORM markup.
    """

    def add_target_and_index(self, name, sig, signode):
        targetname = self.objtype + '-' + name
        if targetname not in self.state.document.ids:
            signode['names'].append(targetname)
            signode['ids'].append(targetname)
            signode['first'] = (not self.names)
            self.state.document.note_explicit_target(signode)

            objects = self.env.domaindata['frm']['objects']
            key = (self.objtype, name)
            if key in objects:
                self.env.warn(self.env.docname,
                              'duplicate description of %s %s, ' %
                              (self.objtype, name) +
                              'other instance in ' +
                              self.env.doc2path(objects[key]),
                              self.lineno)
            objects[key] = self.env.docname
        indextext = self.get_index_text(self.objtype, name)
        if indextext:
            self.indexnode['entries'].append(('single', indextext,
                                              targetname, '', None))

    def get_index_text(self, objectname, name):
        if self.objtype == 'statement':
            return _('%s (statement)') % name
        if self.objtype == 'function':
            return _('%s (function)') % name
        return ''


class ReFORMStatement(ReFORMMarkup):
    """
    Description of a reFORM statement.
    """
    doc_field_types = [
        TypedField('parameter', label=l_('Parameters'),
                   names=('param', 'parameter', 'arg', 'argument'),
                   typerolename='type', typenames=('type',)),
        Field('returnvalue', label=l_('Returns'), has_arg=False,
              names=('returns', 'return')),
    ]

    def handle_signature(self, sig, signode):
        name = sig.strip()
        nameid = name.split()[0]
        desc_name = name
        signode += addnodes.desc_name(nameid, desc_name)
        return nameid


class ReFORMFunction(ReFORMMarkup):
    """
    Description of a reFORM statement.
    """
    doc_field_types = [
        TypedField('parameter', label=l_('Parameters'),
                   names=('param', 'parameter', 'arg', 'argument'),
                   typerolename='type', typenames=('type',)),
        Field('returnvalue', label=l_('Returns'), has_arg=False,
              names=('returns', 'return')),
    ]

    def handle_signature(self, sig, signode):
        # TODO: parse param!
        name = sig.strip()
        nameid = name.split('(')[0]
        desc_name = name
        signode += addnodes.desc_name(nameid, desc_name)
        return nameid


class ReFORMDomain(Domain):
    """reFORM domain."""
    name = 'frm'
    label = 'reFORM'

    object_types = {
        'statement': ObjType(l_('statement'), 'st'),
        'function': ObjType(l_('function'), 'fn'),
    }
    directives = {
        'statement': ReFORMStatement,
        'function': ReFORMFunction,
    }
    roles = {
        'st':  XRefRole(),
        'fn':  XRefRole(),
    }
    initial_data = {
        'objects': {},  # fullname -> docname, objtype
    }

    def clear_doc(self, docname):
        for fullname, doc in list(self.data['objects'].items()):
            if doc == docname:
                del self.data['objects'][fullname]

    def resolve_xref(self, env, fromdocname, builder, typ, target, node,
                     contnode):
        objects = self.data['objects']
        objtypes = self.objtypes_for_role(typ)
        for objtype in objtypes:
            if (objtype, target) in objects:
                return make_refnode(builder, fromdocname,
                                    objects[objtype, target],
                                    objtype + '-' + target,
                                    contnode, target + ' ' + objtype)

    def get_objects(self):
        for (typ, name), docname in self.data['objects'].items():
            yield name, name, typ, docname, typ + '-' + name, 1
