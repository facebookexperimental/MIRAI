#![cfg_attr(not(feature = "std"), no_std)]

/// Edit this file to define custom logic or remove it if it is not needed.
/// Learn more about FRAME and the core library of Substrate FRAME pallets:
/// <https://docs.substrate.io/reference/frame-pallets/>
pub use pallet::*;

#[macro_use]
extern crate mirai_annotations;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;
#[cfg(not(mirai))]
type SecretTaint = ();

#[cfg(mirai)]
mod mock;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;

#[cfg(mirai)]
pub mod mirai;

pub use weights::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use frame_support::error::BadOrigin;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Because this pallet emits events, it depends on the runtime's definition of an event.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// Type representing the weight of this pallet
		type WeightInfo: WeightInfo;
		// Specifies the account that can perform some action
		type ForceOrigin: EnsureOrigin<Self::RuntimeOrigin>;
	}

	// The pallet's runtime storage items.
	// https://docs.substrate.io/main-docs/build/runtime-storage/
	#[pallet::storage]
	#[pallet::getter(fn something)]
	// Learn more about declaring storage items:
	// https://docs.substrate.io/main-docs/build/runtime-storage/#declaring-storage-items
	pub type Something<T> = StorageValue<_, u32>;

	// Pallets use events to inform users when important changes are made.
	// https://docs.substrate.io/main-docs/build/events-errors/
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event documentation should end with an array that provides descriptive names for event
		/// parameters. [something, who]
		SomethingStored { something: u32, who: T::AccountId },
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// Error names should be descriptive.
		NoneValue,
		/// Errors should have helpful documentation associated with them.
		StorageOverflow,
	}

	// Dispatchable functions allows users to interact with the pallet and invoke state changes.
	// These functions materialize as "extrinsics", which are often compared to transactions.
	// Dispatchable functions must be annotated with a weight and must return a DispatchResult.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// An example dispatchable that takes a singles value as a parameter, writes the value to
		/// storage and emits an event. This function must be dispatched by a signed extrinsic.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::do_something())]
		pub fn do_something(origin: OriginFor<T>, something: u32) -> DispatchResult {
			Self::do_something_non_pallet(origin, something)
		}

		/// An example dispatchable that may throw a custom error.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::cause_error())]
		pub fn cause_error(origin: OriginFor<T>) -> DispatchResult {
			let _who = ensure_signed(origin)?;

			// Read a value from storage.
			match <Something<T>>::get() {
				// Return an error if the value has not been set.
				None => return Err(Error::<T>::NoneValue.into()),
				Some(old) => {
					// Increment the value read from storage; will error in the event of overflow.
					let new = old.checked_add(1).ok_or(Error::<T>::StorageOverflow)?;
					// Update the value in storage with the incremented result.
					<Something<T>>::put(new);
					Ok(())
				},
			}
		}
	}

	impl<T: Config> Pallet<T> {

		pub fn do_something_non_pallet(origin: OriginFor<T>, something: u32) -> DispatchResult {
			// Self::sarp_ensure_origin(origin.clone())?;
			// Check that the extrinsic was signed and get the signer.
			// This function will return an error if the extrinsic is not signed.
			// https://docs.substrate.io/main-docs/build/origins/
			// Self::add_tag(&origin);
			let tagged_value = 1;
			let who = Self::sarp_ensure_signed(origin.clone(), &tagged_value)?;

			// add_tag!(&origin, SecretTaint);
			// Self::add_tag(&origin);
			// verify!(has_tag!(&tagged_value, SecretTaint));

			// Update storage.
			// add_tag!(&tagged_value, SecretTaint);
			// Self::verify_has_tag(&tagged_value);
			Self::sarp_put_sensitive_value(origin, something, &tagged_value)?;

			// Emit an event.
			// Self::deposit_event(Event::SomethingStored { something, who });
			// Return a successful DispatchResultWithPostInfo
			Ok(())
		}

		fn sarp_ensure_signed(origin: OriginFor<T>, tagged_value: &u32) -> Result<T::AccountId, BadOrigin> {
			// add_tag!(tagged_value, SecretTaint);
			ensure_signed(origin.clone())
		}

		fn sarp_put_sensitive_value(origin: OriginFor<T>, something: u32, tagged_value: &u32) -> DispatchResult {
			precondition!(has_tag!(tagged_value, SecretTaint));
			// <Something<T>>::put(something);
			Ok(())
		}

		fn verify_has_tag(tagged_value: &u32) {
			// precondition!(false);
			precondition!(has_tag!(tagged_value, SecretTaint));
		}

		fn add_tag(origin: &OriginFor<T>) {
			add_tag!(origin, SecretTaint);
		}
	}
}
