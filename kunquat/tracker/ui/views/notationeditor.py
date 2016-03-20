# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2016
#
# This file is part of Kunquat.
#
# CC0 1.0 Universal, http://creativecommons.org/publicdomain/zero/1.0/
#
# To the extent possible under law, Kunquat Affirmers have waived all
# copyright and related or neighboring rights to Kunquat.
#

from PyQt4.QtCore import *
from PyQt4.QtGui import *

from headerline import HeaderLine


class NotationEditor(QWidget):

    def __init__(self):
        QWidget.__init__(self)

        self._notations = Notations()
        self._octaves = Octaves()
        self._notes = Notes()
        self._note = Note()
        self._keymap = Keymap()

        nlists = QHBoxLayout()
        nlists.setMargin(0)
        nlists.setSpacing(2)
        nlists.addWidget(self._octaves)
        nlists.addWidget(self._notes)
        nlists.addWidget(self._note)

        el = QVBoxLayout()
        el.setMargin(0)
        el.setSpacing(2)
        el.addLayout(nlists)
        el.addWidget(self._keymap)

        separator = QFrame()
        separator.setFrameShape(QFrame.VLine)
        separator.setFrameShadow(QFrame.Sunken)
        separator.setSizePolicy(QSizePolicy.Maximum, QSizePolicy.MinimumExpanding)

        h = QHBoxLayout()
        h.setMargin(0)
        h.setSpacing(4)
        h.addWidget(self._notations)
        h.addWidget(separator)
        h.addLayout(el, 1)
        self.setLayout(h)

    def set_ui_model(self, ui_model):
        self._notations.set_ui_model(ui_model)
        self._octaves.set_ui_model(ui_model)
        self._notes.set_ui_model(ui_model)
        self._note.set_ui_model(ui_model)
        self._keymap.set_ui_model(ui_model)

    def unregister_updaters(self):
        self._keymap.unregister_updaters()
        self._note.unregister_updaters()
        self._notes.unregister_updaters()
        self._octaves.unregister_updaters()
        self._notations.unregister_updaters()


class NotationListToolBar(QToolBar):

    def __init__(self):
        QToolBar.__init__(self)
        self._ui_model = None
        self._updater = None

        self._add_button = QToolButton()
        self._add_button.setText('Add notation')
        self._add_button.setToolTip('Add notation')
        self._add_button.setEnabled(True)

        self._remove_button = QToolButton()
        self._remove_button.setText('Remove notation')
        self._remove_button.setToolTip('Remove notation')
        self._remove_button.setEnabled(False)

        self.addWidget(self._add_button)
        self.addWidget(self._remove_button)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)

        icon_bank = self._ui_model.get_icon_bank()
        self._add_button.setIcon(QIcon(icon_bank.get_icon_path('add')))
        self._remove_button.setIcon(QIcon(icon_bank.get_icon_path('remove')))

        QObject.connect(self._add_button, SIGNAL('clicked()'), self._add_notation)
        QObject.connect(self._remove_button, SIGNAL('clicked()'), self._remove_notation)

        self._update_enabled()

    def unregister_updaters(self):
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        update_signals = set([
            'signal_notation_list', 'signal_notation_editor_selection'])
        if not signals.isdisjoint(update_signals):
            self._update_enabled()

    def _update_enabled(self):
        notation_manager = self._ui_model.get_notation_manager()
        has_custom_notations = len(notation_manager.get_custom_notation_ids()) > 0
        has_selected_notation = bool(notation_manager.get_editor_selected_notation_id())
        self._remove_button.setEnabled(has_custom_notations and has_selected_notation)

    def _add_notation(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation_manager.add_custom_notation()
        self._updater.signal_update(set(['signal_notation_list']))

    def _remove_notation(self):
        notation_manager = self._ui_model.get_notation_manager()
        selected_notation_id = notation_manager.get_editor_selected_notation_id()
        notation_manager.remove_custom_notation(selected_notation_id)
        notation_manager.set_editor_selected_notation_id(None)
        self._updater.signal_update(set(['signal_notation_list']))


class NotationListModel(QAbstractListModel):

    def __init__(self):
        QAbstractListModel.__init__(self)
        self._ui_model = None
        self._updater = None

        self._items = []

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._make_items()

    def unregister_updaters(self):
        pass

    def get_item(self, index):
        row = index.row()
        if 0 <= row < len(self._items):
            item = self._items[row]
            return item
        return None

    def _make_items(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation_ids = notation_manager.get_custom_notation_ids()

        self._items = list((nid, notation_manager.get_notation(nid).get_name())
                for nid in notation_ids)

    def get_index(self, notation_id):
        _, list_index = notation_id
        return self.createIndex(list_index, 0, self._items[list_index])

    # Qt interface

    def rowCount(self, parent):
        return len(self._items)

    def data(self, index, role):
        if role in (Qt.DisplayRole, Qt.EditRole):
            row = index.row()
            if 0 <= row < len(self._items):
                _, name = self._items[row]
                if role == Qt.DisplayRole:
                    vis_name = name or u'-'
                    return QVariant(vis_name)
                elif role == Qt.EditRole:
                    return QVariant(name)
                else:
                    assert False

        return QVariant()

    def headerData(self, section, orientation, role):
        return QVariant()

    def flags(self, index):
        default_flags = QAbstractItemModel.flags(self, index)
        if not index.isValid():
            return default_flags
        if not 0 <= index.row() < len(self._items):
            return default_flags

        return default_flags | Qt.ItemIsEditable

    def setData(self, index, value, role):
        if role == Qt.EditRole:
            if 0 <= index.row() < len(self._items):
                new_name = unicode(value.toString())
                notation_manager = self._ui_model.get_notation_manager()
                notation = notation_manager.get_editor_selected_notation()
                notation.set_name(new_name)
                self._updater.signal_update(set(['signal_notation_list']))
                return True

        return False


class NotationListView(QListView):

    def __init__(self):
        QListView.__init__(self)
        self._ui_model = None
        self._updater = None

        self.setSelectionMode(QAbstractItemView.SingleSelection)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()

    def unregister_updaters(self):
        pass

    def _select_entry(self, cur_index, prev_index):
        item = self.model().get_item(cur_index)
        if item:
            notation_id, _ = item
            notation_manager = self._ui_model.get_notation_manager()
            notation_manager.set_editor_selected_notation_id(notation_id)
            notation_manager.set_editor_selected_octave_id(None)
            self._updater.signal_update(set(['signal_notation_editor_selection']))

    def setModel(self, model):
        QListView.setModel(self, model)

        selection_model = self.selectionModel()

        notation_manager = self._ui_model.get_notation_manager()
        selected_notation_id = notation_manager.get_editor_selected_notation_id()
        if selected_notation_id:
            selection_model.select(
                    model.get_index(selected_notation_id), QItemSelectionModel.Select)

        QObject.connect(
                selection_model,
                SIGNAL('currentChanged(const QModelIndex&, const QModelIndex&)'),
                self._select_entry)


class Notations(QWidget):

    def __init__(self):
        QWidget.__init__(self)
        self._ui_model = None
        self._updater = None

        self._toolbar = NotationListToolBar()

        self._list_model = None
        self._list_view = NotationListView()

        v = QVBoxLayout()
        v.setMargin(0)
        v.setSpacing(2)
        v.addWidget(HeaderLine('Custom notations'))
        v.addWidget(self._toolbar)
        v.addWidget(self._list_view)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)
        self._toolbar.set_ui_model(ui_model)
        self._list_view.set_ui_model(ui_model)

        self._update_model()

    def unregister_updaters(self):
        self._list_view.unregister_updaters()
        self._toolbar.unregister_updaters()
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        if 'signal_notation_list' in signals:
            self._update_model()

    def _update_model(self):
        self._list_model = NotationListModel()
        self._list_model.set_ui_model(self._ui_model)
        self._list_view.setModel(self._list_model)


class OctaveListToolBar(QToolBar):

    def __init__(self):
        QToolBar.__init__(self)
        self._ui_model = None
        self._updater = None

        self._add_button = QToolButton()
        self._add_button.setText('Add octave')
        self._add_button.setToolTip('Add octave')
        self._add_button.setEnabled(True)

        self._remove_button = QToolButton()
        self._remove_button.setText('Remove octave')
        self._remove_button.setToolTip('Remove octave')
        self._remove_button.setEnabled(False)

        self._set_base_button = QToolButton()
        self._set_base_button.setText('Set base')
        self._set_base_button.setEnabled(False)

        self.addWidget(self._add_button)
        self.addWidget(self._remove_button)
        self.addWidget(self._set_base_button)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)

        icon_bank = self._ui_model.get_icon_bank()
        self._add_button.setIcon(QIcon(icon_bank.get_icon_path('add')))
        self._remove_button.setIcon(QIcon(icon_bank.get_icon_path('remove')))

        QObject.connect(self._add_button, SIGNAL('clicked()'), self._add_octave)
        QObject.connect(self._remove_button, SIGNAL('clicked()'), self._remove_octave)
        QObject.connect(
                self._set_base_button, SIGNAL('clicked()'), self._set_base_octave)

        self._update_enabled()

    def unregister_updaters(self):
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        update_signals = set([
            'signal_notation_editor_selection',
            'signal_notation_editor_octaves',
            'signal_notation_editor_octave_selection'])
        if not signals.isdisjoint(update_signals):
            self._update_enabled()

    def _update_enabled(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()
        if not notation:
            self.setEnabled(False)
            return

        self.setEnabled(True)
        has_selected_octave = notation_manager.get_editor_selected_octave_id() != None
        self._remove_button.setEnabled(
                has_selected_octave and notation.get_octave_count() > 1)
        self._set_base_button.setEnabled(has_selected_octave)

    def _add_octave(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()
        notation.add_octave()
        self._updater.signal_update(set(['signal_notation_editor_octaves']))

    def _remove_octave(self):
        notation_manager = self._ui_model.get_notation_manager()
        selected_octave_id = notation_manager.get_editor_selected_octave_id()
        notation = notation_manager.get_editor_selected_notation()
        notation.remove_octave(selected_octave_id)
        base_octave_id = notation.get_base_octave_id()
        if base_octave_id > 0 and base_octave_id >= selected_octave_id:
            notation.set_base_octave_id(base_octave_id - 1)
        notation_manager.set_editor_selected_octave_id(max(0, selected_octave_id - 1))
        self._updater.signal_update(set([
            'signal_notation_editor_octaves',
            'signal_notation_editor_octave_selection']))

    def _set_base_octave(self):
        notation_manager = self._ui_model.get_notation_manager()
        selected_octave_id = notation_manager.get_editor_selected_octave_id()
        notation = notation_manager.get_editor_selected_notation()
        notation.set_base_octave_id(selected_octave_id)
        self._updater.signal_update(set(['signal_notation_editor_octaves']))


class OctaveListModel(QAbstractListModel):

    def __init__(self):
        QAbstractListModel.__init__(self)
        self._ui_model = None
        self._updater = None

        self._items = []

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._make_items()

    def unregister_updaters(self):
        pass

    def get_item(self, index):
        row = index.row()
        if 0 <= row < len(self._items):
            item = self._items[row]
            return item
        return None

    def _make_items(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()

        if notation:
            octave_count = notation.get_octave_count()
            self._items = [notation.get_octave_name(i) for i in xrange(octave_count)]
        else:
            self._items = []

    def get_index(self, octave_index):
        return self.createIndex(octave_index, 0, self._items[octave_index])

    # Qt interface

    def rowCount(self, parent):
        return len(self._items)

    def data(self, index, role):
        if role in (Qt.DisplayRole, Qt.EditRole):
            row = index.row()
            if 0 <= row < len(self._items):
                name = self._items[row]
                if role == Qt.DisplayRole:
                    vis_name = name or u'-'
                    notation_manager = self._ui_model.get_notation_manager()
                    notation = notation_manager.get_editor_selected_notation()
                    if row == notation.get_base_octave_id():
                        vis_name += u' *'
                    return QVariant(vis_name)
                elif role == Qt.EditRole:
                    return QVariant(name)
                else:
                    assert False

        return QVariant()

    def headerData(self, section, orientation, role):
        return QVariant()

    def flags(self, index):
        default_flags = QAbstractItemModel.flags(self, index)
        if not index.isValid():
            return default_flags
        if not 0 <= index.row() < len(self._items):
            return default_flags

        return default_flags | Qt.ItemIsEditable

    def setData(self, index, value, role):
        if role == Qt.EditRole:
            if 0 <= index.row() < len(self._items):
                new_name = unicode(value.toString())
                notation_manager = self._ui_model.get_notation_manager()
                notation = notation_manager.get_editor_selected_notation()
                notation.set_octave_name(index.row(), new_name)
                self._updater.signal_update(set(['signal_notation_editor_octaves']))
                return True

        return False


class OctaveListView(QListView):

    def __init__(self):
        QListView.__init__(self)
        self._ui_model = None
        self._updater = None

        self.setSelectionMode(QAbstractItemView.SingleSelection)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()

    def unregister_updaters(self):
        pass

    def _select_entry(self, cur_index, prev_index):
        item = self.model().get_item(cur_index)
        if item != None:
            notation_manager = self._ui_model.get_notation_manager()
            notation_manager.set_editor_selected_octave_id(cur_index.row())
            self._updater.signal_update(set(['signal_notation_editor_octave_selection']))

    def setModel(self, model):
        QListView.setModel(self, model)

        selection_model = self.selectionModel()

        notation_manager = self._ui_model.get_notation_manager()
        selected_octave_id = notation_manager.get_editor_selected_octave_id()
        if selected_octave_id != None:
            selection_model.select(
                    model.get_index(selected_octave_id), QItemSelectionModel.Select)

        QObject.connect(
                selection_model,
                SIGNAL('currentChanged(const QModelIndex&, const QModelIndex&)'),
                self._select_entry)


class Octaves(QWidget):

    def __init__(self):
        QWidget.__init__(self)
        self._ui_model = None
        self._updater = None

        self._toolbar = OctaveListToolBar()

        self._list_model = None
        self._list_view = OctaveListView()

        v = QVBoxLayout()
        v.setMargin(0)
        v.setSpacing(2)
        v.addWidget(HeaderLine('Octaves'))
        v.addWidget(self._toolbar)
        v.addWidget(self._list_view)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)
        self._toolbar.set_ui_model(ui_model)
        self._list_view.set_ui_model(ui_model)

        self._update_model()
        self._update_enabled()

    def unregister_updaters(self):
        self._list_view.unregister_updaters()
        self._toolbar.unregister_updaters()
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        model_update_signals = set([
            'signal_notation_editor_selection', 'signal_notation_editor_octaves'])
        if not signals.isdisjoint(model_update_signals):
            self._update_model()
            self._update_enabled()
        if 'signal_notation_editor_octave_selection' in signals:
            self._update_enabled()

    def _update_model(self):
        self._list_model = OctaveListModel()
        self._list_model.set_ui_model(self._ui_model)
        self._list_view.setModel(self._list_model)

    def _update_enabled(self):
        notation_manager = self._ui_model.get_notation_manager()
        self.setEnabled(notation_manager.get_editor_selected_notation_id() != None)


class NoteListToolBar(QToolBar):

    def __init__(self):
        QToolBar.__init__(self)
        self._ui_model = None
        self._updater = None

        self._add_button = QToolButton()
        self._add_button.setText('Add note')
        self._add_button.setToolTip('Add note')
        self._add_button.setEnabled(True)

        self._remove_button = QToolButton()
        self._remove_button.setText('Remove note')
        self._remove_button.setToolTip('Remove note')
        self._remove_button.setEnabled(False)

        self.addWidget(self._add_button)
        self.addWidget(self._remove_button)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)

        icon_bank = self._ui_model.get_icon_bank()
        self._add_button.setIcon(QIcon(icon_bank.get_icon_path('add')))
        self._remove_button.setIcon(QIcon(icon_bank.get_icon_path('remove')))

        QObject.connect(self._add_button, SIGNAL('clicked()'), self._add_note)
        QObject.connect(self._remove_button, SIGNAL('clicked()'), self._remove_note)

        self._update_enabled()

    def unregister_updaters(self):
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        update_signals = set([
            'signal_notation_editor_selection',
            'signal_notation_editor_notes',
            'signal_notation_editor_note_selection'])
        if not signals.isdisjoint(update_signals):
            self._update_enabled()

    def _update_enabled(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()
        if not notation:
            self.setEnabled(False)
            return

        self.setEnabled(True)
        has_selected_note = notation_manager.get_editor_selected_note_index() != None
        has_notes = bool(notation.get_notes())
        self._remove_button.setEnabled(has_selected_note and has_notes)

    def _add_note(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()
        notation.add_note()
        self._updater.signal_update(set(['signal_notation_editor_notes']))

    def _remove_note(self):
        notation_manager = self._ui_model.get_notation_manager()
        note_index = notation_manager.get_editor_selected_note_index()
        notation = notation_manager.get_editor_selected_notation()
        notation.remove_note(note_index)
        notation_manager.set_editor_selected_note_index(None)
        self._updater.signal_update(set(['signal_notation_editor_notes']))


class NoteListModel(QAbstractListModel):

    def __init__(self):
        QAbstractListModel.__init__(self)
        self._ui_model = None
        self._updater = None

        self._items = []

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._make_items()

    def unregister_updaters(self):
        pass

    def get_item(self, index):
        row = index.row()
        if 0 <= row < len(self._items):
            item = self._items[row]
            return item
        return None

    def _make_items(self):
        notation_manager = self._ui_model.get_notation_manager()
        notation = notation_manager.get_editor_selected_notation()

        if notation:
            self._items = list(notation.get_notes())
        else:
            self._items = []

    def get_index(self, list_index):
        return self.createIndex(list_index, 0, self._items[list_index])

    # Qt interface

    def rowCount(self, parent):
        return len(self._items)

    def data(self, index, role):
        if role == Qt.DisplayRole:
            row = index.row()
            if 0 <= row < len(self._items):
                _, name = self._items[row]
                vis_name = name or u'-'
                return QVariant(vis_name)

        return QVariant()

    def headerData(self, section, orientation, role):
        return QVariant()


class NoteListView(QListView):

    def __init__(self):
        QListView.__init__(self)
        self._ui_model = None
        self._updater = None

        self.setSelectionMode(QAbstractItemView.SingleSelection)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()

    def unregister_updaters(self):
        pass

    def _select_entry(self, cur_index, prev_index):
        item = self.model().get_item(cur_index)
        if item != None:
            notation_manager = self._ui_model.get_notation_manager()
            notation_manager.set_editor_selected_note_index(cur_index.row())
            self._updater.signal_update(set(['signal_notation_editor_note_selection']))

    def setModel(self, model):
        QListView.setModel(self, model)

        selection_model = self.selectionModel()

        notation_manager = self._ui_model.get_notation_manager()
        selected_note_index = notation_manager.get_editor_selected_note_index()
        if selected_note_index != None:
            selection_model.select(
                    model.get_index(selected_note_index), QItemSelectionModel.Select)

        QObject.connect(
                selection_model,
                SIGNAL('currentChanged(const QModelIndex&, const QModelIndex&)'),
                self._select_entry)


class Notes(QWidget):

    def __init__(self):
        QWidget.__init__(self)
        self._ui_model = None
        self._updater = None

        self._toolbar = NoteListToolBar()

        self._list_model = None
        self._list_view = NoteListView()

        v = QVBoxLayout()
        v.setMargin(0)
        v.setSpacing(2)
        v.addWidget(HeaderLine('Notes'))
        v.addWidget(self._toolbar)
        v.addWidget(self._list_view)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)
        self._toolbar.set_ui_model(ui_model)
        self._list_view.set_ui_model(ui_model)

        self._update_model()
        self._update_enabled()

    def unregister_updaters(self):
        self._list_view.unregister_updaters()
        self._toolbar.unregister_updaters()
        self._updater.unregister_updater(self._perform_updates)

    def _perform_updates(self, signals):
        model_update_signals = set([
            'signal_notation_editor_selection', 'signal_notation_editor_notes'])
        if not signals.isdisjoint(model_update_signals):
            self._update_model()
            self._update_enabled()
        if 'signal_notation_editor_note_selection' in signals:
            self._update_enabled()

    def _update_model(self):
        self._list_model = NoteListModel()
        self._list_model.set_ui_model(self._ui_model)
        self._list_view.setModel(self._list_model)

    def _update_enabled(self):
        notation_manager = self._ui_model.get_notation_manager()
        self.setEnabled(notation_manager.get_editor_selected_notation_id() != None)


class Note(QWidget):

    def __init__(self):
        QWidget.__init__(self)

        v = QVBoxLayout()
        v.setMargin(0)
        v.setSpacing(2)
        v.addWidget(HeaderLine('Current note'))
        v.addStretch(1)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        pass

    def unregister_updaters(self):
        pass


class Keymap(QWidget):

    def __init__(self):
        QWidget.__init__(self)

        v = QVBoxLayout()
        v.setMargin(0)
        v.setSpacing(2)
        v.addWidget(HeaderLine('Keymap'))
        v.addStretch(1)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        pass

    def unregister_updaters(self):
        pass


