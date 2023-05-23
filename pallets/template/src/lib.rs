#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

/// Edit this file to define custom logic or remove it if it is not needed.
/// Learn more about FRAME and the core library of Substrate FRAME pallets:
/// <https://docs.substrate.io/reference/frame-pallets/>
pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

mod methods;

#[cfg(feature="risc_v")]
pub mod risc_0 {
	#[macro_use]
	use alloc::{
		vec,
		string::String
	};
	use risc0_zkp::{
		core::{
			digest::{DIGEST_BYTES, DIGEST_WORDS},
			hash::sha::{BLOCK_BYTES, BLOCK_WORDS},
			log2_ceil,
		},
		ZK_CYCLES,
	};
	use risc0_zkvm_platform::{
		fileno,
		memory::MEM_SIZE,
		syscall::{
			ecall, halt,
			reg_abi::{REG_A0, REG_A1, REG_A2, REG_A3, REG_A4, REG_T0},
		},
		PAGE_SIZE, WORD_SIZE,
	};
	pub use rrs_lib::{
		memories::VecMemory,
		instruction_executor::{
			InstructionExecutor,
			InstructionTrap
		}, 
		HartState,
		MemAccessSize, 
		Memory,
		instruction_string_outputter::InstructionStringOutputter,
		InstructionProcessor,
		csrs::{CSRAddr, ExceptionCause, MIx, PrivLevel},
	};
	use risc0_zkvm::binfmt::image::{
		PageTableInfo,
		MemoryImage
	};

	pub fn instruction_executor<'a>(hart: &'a mut HartState, mem: &'a mut VecMemory) -> InstructionExecutor<'a, VecMemory> {
		hart.pc = 0;
		InstructionExecutor {
			hart_state: hart,
			mem: mem,
		}
	}

	pub fn output_disass<M: Memory>(executor: &mut InstructionExecutor<M>) -> String {
		let mut outputter = InstructionStringOutputter { insn_pc: executor.hart_state.pc };
		let insn_bits = executor.mem.read_mem(executor.hart_state.pc, MemAccessSize::Word).unwrap();
		rrs_lib::process_instruction(&mut outputter, insn_bits).unwrap()
	}

}

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use frame_support::log;
	use frame_system::offchain::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: CreateSignedTransaction<Call<Self>> + frame_system::Config {
		/// Because this pallet emits events, it depends on the runtime's definition of an event.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
		// type AuthorityId: AppCrypto<Self::Public, Self::Signature>;
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

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Offchain worker entry point.
		///
		/// By implementing `fn offchain_worker` you declare a new offchain worker.
		/// This function will be called when the node is fully synced and a new best block is
		/// successfully imported.
		/// Note that it's not guaranteed for offchain workers to run on EVERY block, there might
		/// be cases where some blocks are skipped, or for some the worker runs twice (re-orgs),
		/// so the code should be able to handle that.
		fn offchain_worker(block_number: T::BlockNumber) {
			log::info!("Hello from pallet-ocw.");
			// The entry point of your code called by offchain worker
			#[macro_use]
			use alloc::{
				vec,
				string::String
			};
			#[cfg(feature="risc_v")]
			{
				let mut hart = super::risc_0::HartState::new();
				let mut mem = super::risc_0::VecMemory::new(vec![0x1234b137, 0xf387e1b7, 0x003100b3]);
				let mut executor = super::risc_0::instruction_executor(&mut hart, &mut mem);

				#[cfg(feature="test_assertions")]
				{
					// Test assert : Execute first instruction
					log::info!("{}",super::risc_0::output_disass(&mut executor));
					assert_eq!(executor.step(), Ok(()));
					assert_eq!(executor.hart_state.registers[2], 0x1234b000);

					// Test assert : Execute first instruction
					super::risc_0::output_disass(&mut executor);
					assert_eq!(executor.step(), Ok(()));
					assert_eq!(executor.hart_state.registers[3], 0xf387e000);

					// Test assert : Execute first instruction
					super::risc_0::output_disass(&mut executor);
					assert_eq!(executor.step(), Ok(()));
					assert_eq!(executor.hart_state.registers[1], 0x05bc9000);

					// Memory only contains three instructions so next step will produce a fetch error
					assert_eq!(executor.step(), Err(super::risc_0::InstructionTrap::Exception(
						super::risc_0::ExceptionCause::InstructionAccessFault,
						0,
					)));

					assert_eq!(1, 0); // should panic.
				}

			}

			
		}
		// ...
	}

	// Dispatchable functions allows users to interact with the pallet and invoke state changes.
	// These functions materialize as "extrinsics", which are often compared to transactions.
	// Dispatchable functions must be annotated with a weight and must return a DispatchResult.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// An example dispatchable that takes a singles value as a parameter, writes the value to
		/// storage and emits an event. This function must be dispatched by a signed extrinsic.
		#[pallet::call_index(0)]
		#[pallet::weight(10_000 + T::DbWeight::get().writes(1).ref_time())]
		pub fn do_something(origin: OriginFor<T>, something: u32) -> DispatchResult {
			// Check that the extrinsic was signed and get the signer.
			// This function will return an error if the extrinsic is not signed.
			// https://docs.substrate.io/main-docs/build/origins/
			let who = ensure_signed(origin)?;

			// Update storage.
			<Something<T>>::put(something);

			// Emit an event.
			Self::deposit_event(Event::SomethingStored { something, who });
			// Return a successful DispatchResultWithPostInfo
			Ok(())
		}

		/// An example dispatchable that may throw a custom error.
		#[pallet::call_index(1)]
		#[pallet::weight(10_000 + T::DbWeight::get().reads_writes(1,1).ref_time())]
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


}
