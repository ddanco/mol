#!/usr/bin/env python3

from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, Optional, Tuple


Vertex = str
Arc = Tuple[Vertex, Vertex, 'str']
Tolls = Callable[[Arc], float]


@dataclass
class Graph:
  vertices: FrozenSet[Vertex]
  # Includes name to distinguish arcs with identical vertices
  arcs: FrozenSet[Tuple[Vertex, Vertex, str]]


@dataclass
class Latencies:
  latencies: Dict[Arc, Callable[[float], float]]

  def __call__(self, arc: Arc) -> Callable[[float], float]:
    return self.latencies[arc]


@dataclass
class Commodity:
  pair: Tuple[Vertex, Vertex]
  demand: float


@dataclass
class SelfishRoutingInstance:
  graph: Graph
  latencies: Latencies
  commodities: Tuple[Commodity, ...]


@dataclass
class Flow:
  flow: Dict[Arc, Callable[[float], float]]

  def __call__(self, arc: Arc) -> Callable[[float], float]:
    return self.flow[arc]


def get_optimal_flow(instance: SelfishRoutingInstance) -> Flow:
  # As this is not the focus of the problem, and we have
  # the solution already described in the lecture notes,
  # I am omitting this algorithm.
  ...


def calculate_tolls_from_flows(
    # nash_flow: Flow,
    instance: SelfishRoutingInstance,
    optimal_flow: Flow,
    sensitivity: float) -> Tolls:

  def get_arc_latency(arc: Arc) -> float:
    return instance.latencies(arc)(optimal_flow(arc)(2.0)) # FIXME

  max_latency = -1.0
  for arc in optimal_flow.flow:
    if get_arc_latency(arc) > max_latency:
      max_latency = get_arc_latency(arc)
      print('max: ', max_latency)

  def calculate_toll(arc: Arc) -> float:
    if optimal_flow(arc)(2.0) == 0: # FIXME
      return 0.0
    print('latency, ', get_arc_latency(arc))
    return (max_latency - get_arc_latency(arc)) / sensitivity

  return lambda A: calculate_toll(A)


def get_tolls(instance: SelfishRoutingInstance, sensitivity: float) -> Tolls:
  return calculate_tolls_from_flows(
    instance,
    get_optimal_flow(instance),
    sensitivity)


def print_tolls(instance: SelfishRoutingInstance, tolls: Tolls) -> None:
  print('Tolls per arc:\n')
  for arc in instance.graph.arcs:
    print(f'Arc: {arc}, Toll: {tolls(arc)}')


if __name__ == '__main__':

  # I know this all wasn't necessary. I just miss coding.

  pigou_graph = Graph(
    vertices=frozenset({'s', 't'}),
    arcs=frozenset({('s', 't', 'top'), ('s', 't', 'bottom')}))

  pigou_latencies = Latencies({
    ('s', 't', 'top'): lambda x: x,
    ('s', 't', 'bottom'): lambda x: 4.0})

  example_instance = SelfishRoutingInstance(
    pigou_graph,
    pigou_latencies,
    (Commodity(('s', 't'), 4),))

  example_optimal_flow = Flow({
    ('s', 't', 'top'): lambda x: 0.5*x,
    ('s', 't', 'bottom'): lambda x: 0.5*x})
  example_sensitivity = 1

  # For this example, we provide the flow, but if get_optimal_flow
  # were implemented, we would call get_tolls
  print_tolls(
    example_instance,
    calculate_tolls_from_flows(
      example_instance,
      example_optimal_flow,
      example_sensitivity))

  ##################
  # Output when run:

  # Tolls per arc:

  # Arc: ('s', 't', 'top'), Toll: 0.5
  # Arc: ('s', 't', 'bottom'), Toll: 0.0

  ##################
