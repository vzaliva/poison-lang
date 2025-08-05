# Drone Dual Control System Example

## Overview

This example demonstrates a drone control system with two independent control
subsystems: altitude control and lateral position control. The system shows how
poison tracking models fault propagation and how de-poisoning predicates can
recover from certain types of faults.

## System Architecture

The drone control system consists of two main components:

1. **Altitude Control System**: Manages the drone's vertical position and landing procedures
2. **Lateral Position Control System**: Manages the drone's horizontal position relative to a central divider

### Key Design Principle: Independence

The fundamental design principle is that **altitude control and lateral position control are completely independent**. This means:
- Faults in altitude-related sensors cannot affect lateral position control
- Faults in lateral position sensors cannot affect altitude control
- Each subsystem can operate correctly even when the other subsystem is experiencing faults

## Fault Sources and De-poisoning

### Barometer Faults
The barometer reading could be fault and returns a poisoned value when it fails.
This represents a faulty sensor that can propagate poison through the altitude
control system. The altitude control system may consume these poisoned values
when initiating landing procedures.

### User Inputs and Fault Sources
The system simulates two distinct user inputs:

1. **Landing Initiation**: A boolean command indicating whether the user wants
   to land. This input is never faulty and always returns clean values.

2. **Lateral Position Control**: A position adjustment command that may be
   faulty. The lateral position control system demonstrates de-poisoning through
   predicates. This user control input uses a simulated random generator that
   may return poisoned values. However, the system includes a de-poisoning
   predicate that checks if the adjustment value falls within a valid range (0
   to 200). When the predicate is satisfied, the poisoned value is de-poisoned
   and used normally. If the predicate fails, the system gracefully skips the
   faulty input and maintains the current position.

## Control Logic

### Altitude Control
The altitude control system checks if the user wants to land and if the altitude
is below the landing threshold. It may consume poisoned values from the
barometer when initiating landing, but maintains altitude independently when not
landing.

### Lateral Position Control
The lateral position control takes a position value and holds that position. It
does not depend on altitude sensor data and operates independently of altitude
control decisions. The system includes de-poisoning mechanisms to handle faulty
user inputs gracefully.

## Poison Propagation and Recovery

### Poison Sources
1. **Barometer Fault**: Returns poisoned values when it fails
2. **Lateral Position Control Fault**: May return poisoned values from the simulated random generator (landing initiation is never faulty)

### De-poisoning Mechanisms
The lateral position control demonstrates active fault recovery through
de-poisoning predicates. When user input is potentially poisoned, the system
applies a range check predicate. If the value falls within the expected range,
it is de-poisoned and used normally. This allows the system to recover from
certain types of sensor faults while maintaining safety.

### Independence Verification
The altitude control function may consume poisoned values from the barometer,
but the lateral position control operates on completely independent data
sources. Even when the barometer is faulty and returning poisoned values, the
lateral position control continues to function correctly due to its independence
and de-poisoning mechanisms.

## Fault Tolerance Properties

## Key Insights

1. **Subsystem Independence**: The design ensures that altitude and lateral position control are truly independent
2. **Poison Tracking**: The type system tracks poison propagat
3. **De-poisoning Recovery**: Predicate-based de-poisoning allows graceful recovery from certain faults
4. **Fault Isolation**: Lateral position control remains functional even when altitude sensors are faulty

## Conclusion

This example demonstrates how poison tracking can be used to model fault
propagation in safety-critical systems. The independence between altitude and
lateral position control, combined with de-poisoning mechanisms, ensures robust
fault tolerance through design rather than just error handling. 