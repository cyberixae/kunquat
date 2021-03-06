# -*- coding: utf-8 -*-

#
# Authors: Tomi Jylhä-Ollila, Finland 2014
#          Toni Ruottu, Finland 2014
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

import kunquat.tracker.cmdline as cmdline
from kunquat.tracker.ui.identifiers import *
from mainwindow import MainWindow
from aboutwindow import AboutWindow
from eventlist import EventList


class RootView():

    def __init__(self):
        self._ui_model = None
        self._task_executer = None
        self._updater = None
        self._visible = set()
        self._main_window = MainWindow()
        self._about_window = None
        self._event_log = None
        self._module = None

    def set_ui_model(self, ui_model):
        self._ui_model = ui_model
        self._main_window.set_ui_model(ui_model)
        self._updater = self._ui_model.get_updater()
        self._updater.register_updater(self._perform_updates)
        self._module = self._ui_model.get_module()

    def show_main_window(self):
        visibility_manager = self._ui_model.get_visibility_manager()
        visibility_manager.show_main()

    def setup_module(self):
        module = self._ui_model.get_module()
        module_path = cmdline.get_kqt_file()
        if module_path:
            module.set_path(module_path)
            module.execute_load(self._task_executer)
        else:
            module.execute_create_sandbox(self._task_executer)

    def set_task_executer(self, task_executer):
        self._task_executer = task_executer

    def _perform_updates(self, signals):
        visibility_manager = self._ui_model.get_visibility_manager()
        visibility_update = visibility_manager.get_visible()

        opened = visibility_update - self._visible
        closed = self._visible - visibility_update

        for ui in opened:
            # Check settings for UI visibility
            is_show_allowed = visibility_manager.is_show_allowed()

            if ui == UI_MAIN:
                if is_show_allowed:
                    self._main_window.show()
            elif ui == UI_ABOUT:
                self._about_window = AboutWindow()
                self._about_window.set_ui_model(self._ui_model)
                if is_show_allowed:
                    self._about_window.show()
            elif ui == UI_EVENT_LOG:
                self._event_log = EventList()
                self._event_log.set_ui_model(self._ui_model)
                if is_show_allowed:
                    self._event_log.show()

        for ui in closed:
            if ui == UI_MAIN:
                visibility_manager.hide_all()
                self._main_window.hide()
            elif ui == UI_ABOUT:
                self._about_window.unregister_updaters()
                self._about_window.deleteLater()
                self._about_window = None
            elif ui == UI_EVENT_LOG:
                self._event_log.unregister_updaters()
                self._event_log.deleteLater()
                self._event_log = None

        self._visible = set(visibility_update)

        if self._visible:
            if 'signal_start_save_module' in signals:
                self._start_save_module()
            if 'signal_save_module_finished' in signals:
                self._on_save_module_finished()
        else:
            QApplication.quit()

        self._ui_model.clock()

    def unregister_updaters(self):
        self._updater.unregister_updater(self._perform_updates)
        self._main_window.unregister_updaters()

    def _start_save_module(self):
        self._main_window.setEnabled(False)
        self._module.flush(self._execute_save_module)

    def _execute_save_module(self):
        task = self._module.execute_save(self._task_executer)

    def _on_save_module_finished(self):
        self._module.finish_save()
        self._main_window.setEnabled(True)


