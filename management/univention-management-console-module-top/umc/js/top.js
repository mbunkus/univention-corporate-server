/*global console MyError dojo dojox dijit umc */

dojo.provide("umc.modules.top");

dojo.require("dijit.layout.BorderContainer");
dojo.require("umc.i18n");
dojo.require("umc.tools");
dojo.require("umc.widgets.Form");
dojo.require("umc.widgets.Grid");
dojo.require("umc.widgets.Module");
dojo.require("umc.widgets.SearchForm");
dojo.require("umc.widgets.StandbyMixin");

dojo.declare("umc.modules.top", [ umc.widgets.Module, umc.i18n.Mixin ], {

	_grid: null,
	_store: null,
	_searchWidget: null,
	_contextVariable: null,
	_layoutContainer: null,

	idProperty: 'pid',

	i18nClass: 'umc.modules.top',

	buildRendering: function() {
		this.inherited(arguments);

		this._layoutContainer = new dijit.layout.BorderContainer({});
		this.addChild(this._layoutContainer);

		var actions = [{
			name: 'delete',
			label: this._('Kill processes'),
			iconClass: 'dijitIconDelete',
			callback: dojo.hitch(this, function(ids) {
				var params = {
					signal: 'SIGTERM',
					pid: ids
				};
                this.umcpCommand('top/kill', params).then(dojo.hitch(this, function(data) {
					umc.app.notify(this._('Processes killed successfully'));
				}));
			})
		}];

		var columns = [{
			name: 'user',
			label: this._('User'),
            width: '10%'
		}, {
			name: 'pid',
			label: this._('PID'),
            width: '10%'
		}, {
			name: 'cpu',
			label: this._('CPU'),
            width: '10%'
		}, {
			name: 'vsize',
			label: this._('Virtual size'),
            width: '10%'
		}, {
			name: 'rssize',
			label: this._('Resident set size'),
            width: '10%'
		}, {
			name: 'mem',
			label: this._('Memory in %'),
            width: '10%'
		}, {
			name: 'prog',
			label: this._('Program'),
            width: '10%'
		}, {
			name: 'command',
			label: this._('Command'),
            width: 'auto'
		}];

		this._grid = new umc.widgets.Grid({
			region: 'center',
			actions: actions,
			columns: columns,
			moduleStore: this.moduleStore,
			query: {
                category: 'all',
                filter: '*'
            }
		});
		this._layoutContainer.addChild(this._grid);

		var widgets = [{
			type: 'ComboBox',
			name: 'category',
			value: 'all',
			label: this._('Category'),
			staticValues: [
				{id: 'all', label: this._('All')},
				{id: 'user', label: this._('User')},
				{id: 'pid', label: this._('PID')},
				{id: 'prog', label: this._('Program')},
				{id: 'command', label: this._('Command')}
			]
		}, {
			type: 'TextBox',
			name: 'filter',
			value: '*',
			label: this._('Keyword')
		}];

		this._searchWidget = new umc.widgets.SearchForm({
			region: 'top',
			widgets: widgets,
			layout: [['category', 'filter']],
			onSearch: dojo.hitch(this._grid, 'filter')
		});


		this._layoutContainer.addChild(this._searchWidget);

		this._layoutContainer.startup();
    }
});
