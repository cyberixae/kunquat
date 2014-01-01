# -*- coding: utf-8 -*-

#
# Author: Tomi Jylhä-Ollila, Finland 2013-2014
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


class EventListModel(QAbstractTableModel):

    HEADERS = ["#", "Channel", "Type", "Value", "Context"]

    def __init__(self):
        QAbstractTableModel.__init__(self)
        self._ui_model = None
        self._updater = None

        self._log = []

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._updater = ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)

    def _perform_updates(self, signals):
        event_history = self._ui_model.get_event_history()
        log = event_history.get_log()

        oldlen = len(self._log)
        newlen = len(log)
        if oldlen < newlen:
            self.beginInsertRows(QModelIndex(), 0, newlen - oldlen - 1)
            self._log = log
            self.endInsertRows()
        elif oldlen > newlen:
            self.beginRemoveRows(QModelIndex(), 0, oldlen - newlen - 1)
            self._log = log
            self.endRemoveRows()
        else:
            self._log = log

        QObject.emit(
                self,
                SIGNAL('dataChanged(QModelIndex, QModelIndex)'),
                self.index(0, 0),
                self.index(len(self._log) - 1, len(self.HEADERS) - 1))

    # Qt interface

    def rowCount(self, parent):
        if parent.isValid():
            return 0
        return len(self._log)

    def columnCount(self, parent):
        if parent.isValid():
            return 0
        return len(self.HEADERS)

    def data(self, index, role):
        if role == Qt.DisplayRole:
            row, column = index.row(), index.column()
            if 0 <= column < len(self.HEADERS) and 0 <= row < len(self._log):
                return QVariant(self._log[len(self._log) - row - 1][column])

        return QVariant()

    def headerData(self, section, orientation, role):
        if role == Qt.DisplayRole:
            if orientation == Qt.Horizontal:
                if 0 <= section < len(self.HEADERS):
                    return QVariant(self.HEADERS[section])

        return QVariant()


class EventList(QWidget):

    def __init__(self):
        QWidget.__init__(self)
        self._ui_model = None

        self._logmodel = EventListModel()

        v = QVBoxLayout()
        self._tableview = QTableView()
        self._tableview.setModel(self._logmodel)
        v.addWidget(self._tableview)
        self.setLayout(v)

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._logmodel.set_ui_model(ui_model)


