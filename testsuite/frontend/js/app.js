// Generated by CoffeeScript 1.4.0
(function() {

  window.hipspec_module = angular.module('hipspec', []);

  hipspec_module.filter('seconds', function() {
    return function(s) {
      if (s != null) {
        return s.toFixed(2);
      } else {
        return "";
      }
    };
  });

  hipspec_module.filter('ppresfile', function() {
    return function(s) {
      s = s.replace(/^results\//, function() {
        return "";
      });
      s = s.replace(/.json$/, function() {
        return "";
      });
      return s.replace(/_/g, function() {
        return " ";
      });
    };
  });

  hipspec_module.factory('config', function() {
    return [
      {
        short: 'prod',
        name: 'Productive Use of Failure',
        files: ['Definitions.hs', 'Properties.hs']
      }, {
        short: 'zeno',
        name: 'Zeno/IsaPlanner',
        files: ['Definitions.hs', 'Properties.hs']
      }, {
        short: 'mini',
        name: 'Mini',
        files: ['Mini.hs']
      }, {
        short: 'examples',
        name: 'Examples',
        files: ['AppendLists.hs', 'BinLists.hs', 'Implies.hs', 'ListMonad.hs', 'Nat.hs', 'Nicomachus.hs', 'Reverse.hs', 'Rotate.hs']
      }, {
        short: 'precision-recall',
        name: 'Precision/Recall',
        files: []
      }
    ];
  });

  hipspec_module.factory('request', function($http) {
    return {
      list: function(testsuite) {
        return $http.get("" + testsuite.short + "/json_list");
      },
      log: function(testsuite, instance) {
        return $http.get("" + testsuite.short + "/" + instance);
      }
    };
  });

  hipspec_module.controller('TestsuiteCtrl', function($scope, config) {
    $scope.empty = _.isEmpty;
    $scope.testsuites = config;
    $scope.testsuite = void 0;
    return $scope.setTestsuite = function(t) {
      return $scope.testsuite = t;
    };
  });

  hipspec_module.controller('CompareCtrl', function($scope, request, $http, $q) {
    var empty, process_results;
    $scope.content = "";
    $scope.viewFile = function(dir, file) {
      return $http.get("" + dir + "/" + file).success(function(res) {
        return $scope.content = res;
      });
    };
    empty = function() {
      $scope.table = {};
      $scope.headers = {};
      $scope.num_solved = 0;
      return $scope.solved = {};
    };
    $scope.display_prop = function(prop) {
      return prop.replace(/^prop_/, "");
    };
    $scope.num_problems = function() {
      return _.size($scope.headers);
    };
    $scope.results = {};
    process_results = function() {
      var headers, i, log, message, num_solved, obj, prop, res, solved, table, time, type, _i, _j, _k, _len, _len1, _len2, _ref, _ref1, _ref2, _ref3, _ref4;
      table = {};
      headers = {};
      num_solved = 0;
      solved = {};
      _ref = $scope.results;
      for (i in _ref) {
        log = _ref[i];
        for (_i = 0, _len = log.length; _i < _len; _i++) {
          _ref1 = log[_i], time = _ref1[0], message = _ref1[1];
          _ref2 = _.pairs(message)[0], type = _ref2[0], obj = _ref2[1];
          res = {};
          if (type === "Finished") {
            _ref3 = obj.unproved;
            for (_j = 0, _len1 = _ref3.length; _j < _len1; _j++) {
              prop = _ref3[_j];
              headers[prop] = {};
              res[prop] = {
                solved: false,
                failed: true
              };
            }
            _ref4 = obj.proved;
            for (_k = 0, _len2 = _ref4.length; _k < _len2; _k++) {
              prop = _ref4[_k];
              headers[prop] = {};
              res[prop] = {
                solved: true,
                failed: false
              };
              if (res[prop].solved && !solved[prop]) {
                solved[prop] = true;
                num_solved++;
              }
            }
            res.time = time;
          }
        }
        table[i] = res;
      }
      $scope.headers = headers;
      $scope.table = table;
      $scope.num_solved = num_solved;
      return $scope.solved = solved;
    };
    return $scope.$watch('testsuite', function() {
      if ($scope.testsuite != null) {
        return request.list($scope.testsuite).success(function(list) {
          var i;
          empty();
          return $q.all((function() {
            var _i, _len, _results;
            _results = [];
            for (_i = 0, _len = list.length; _i < _len; _i++) {
              i = list[_i];
              _results.push(request.log($scope.testsuite, i));
            }
            return _results;
          })()).then(function(logs) {
            $scope.results = _.object(list, _.map(logs, function(res) {
              return res.data;
            }));
            return process_results();
          });
        });
      }
    });
  });

  hipspec_module.controller('ExplorationCtrl', function($scope) {
    $scope.equations = [];
    $scope.explored = false;
    $scope.processed = false;
    $scope.exploration_time = 0;
    return $scope.is_explored = function(instance) {
      var message, obj, time, type, _i, _len, _ref, _ref1, _ref2;
      if (!$scope.processed) {
        _ref = $scope.results[instance];
        for (_i = 0, _len = _ref.length; _i < _len; _i++) {
          _ref1 = _ref[_i], time = _ref1[0], message = _ref1[1];
          _ref2 = _.pairs(message)[0], type = _ref2[0], obj = _ref2[1];
          if (type === "ExploredTheory") {
            $scope.equations = obj.equations;
            $scope.explored = true;
            $scope.exploration_time = time;
            break;
          }
        }
        $scope.processed = true;
      }
      return $scope.explored;
    };
  });

  hipspec_module.controller('InstanceCtrl', function($scope) {
    $scope.interestingType = function(type) {
      return String(_.contains(["FileProcessed", "QuickSpecDone", "InductiveProof", "PlainProof", "Finished", "ExploredTheory"], type));
    };
    $scope.result = [];
    $scope.show = false;
    return $scope.toggle_shown = function(instance) {
      var message, obj, res, time, type, x, _i, _len, _ref, _ref1;
      $scope.show = !$scope.show;
      x = $scope.results[instance];
      res = [];
      for (_i = 0, _len = x.length; _i < _len; _i++) {
        _ref = x[_i], time = _ref[0], message = _ref[1];
        _ref1 = _.pairs(message)[0], type = _ref1[0], obj = _ref1[1];
        if (_.isArray(obj)) {
          obj = {};
        }
        obj.time = time;
        obj.type = type;
        res.push(obj);
      }
      return $scope.result = res;
    };
  });

}).call(this);
